"""Focused formal submissions through unchanged host launcher, one module per scope."""
from NMB_transport import *
import hashlib,re,shlex,sys,lzma
sha=lambda b:hashlib.sha256(b).hexdigest()
def run(a,kind,target,command=None,extra=None,env_extra=None):
    assert ((a.startswith('NMB_L') and 1<=int(a[-3:])<=140) or (a.startswith('NMB_K') and 1<=int(a[-3:])<=40)) and not (E/a).exists()
    env=json.loads((E/'NMB_ENV.json').read_text())['env']
    env['LEAN_PATH']=':'.join([B+'/NMB_objects']+json.loads((E/'NMB_PATHS.json').read_text()))
    env['TMPDIR']=B+'/NMB_tmp'
    env['CARGO_TARGET_DIR']=B+'/NMB_target'
    env['CARGO_NET_OFFLINE']='true'
    env.update(env_extra or {})
    files=dict(extra or {})
    if kind=='lean':
        text=(E/(target+'.lean')).read_text()
        for dep in re.findall(r'^import (NMB_[\w.]+)',text,re.M):
            h=sha((E/(dep+'.lean')).read_bytes())
            assert any(x['module']==dep and x['exit_status']==0 and h in x['source_hashes'].values() for x in [json.loads(l) for l in (E/'NMB_ATTEMPTS.jsonl').read_text().splitlines()]),'Compile current direct import first: '+dep
        src='NMB_generated/'+target.replace('.','/')+'.lean';files[src]=text
        command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMB_generated','-o','NMB_objects/'+target.replace('.','/')+'.olean',src]
        if target in ['NMB_ProofDriver','NMB_ScanDriver']:command+=['-c','NMB_native/'+target+'.c']
    assert command
    cfg=dict(attempt=a,kind=kind,module=target,command=command,env=env,sources=list(files),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time=('focused Lean elaboration' if kind=='lean' else 'optimized Rust compilation then CBMC verification of '+target if kind=='kani' else 'optimized audit link' if kind=='link' else 'named raw axiom/module scan' if kind=='audit' else 'bounded source, metadata, export or hashing inspection'))
    files[a+'.json']=json.dumps(cfg)
    admission(a)
    r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');rels=set();pins={{}}
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*.olean'))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for n,t in files.items():
 if n.endswith('.lean'):
  for line in t.splitlines():
   if line.startswith('import '):rels.update(d.replace('.','/')+'.olean' for d in line[7:].split() if d!='all')
if {kind!r} in ['audit','link','inspect']:rels.update(n+'.olean' for n in ['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations'])
if {kind!r}=='audit':rels.add('NMB_COMBINED_IMPORT.olean')
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']['selected_objects']=pins
if {kind!r}=='audit':
 x['deps_fingerprint']['executables']={{str(p):{{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}}for p in [b/'NMB_native/NMB_ProofDriver',b/'NMB_native/NMB_ScanDriver'] if p.is_file()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x,indent=1)+'\\n')
(b/'NMB_objects'/{target.replace('.','/')!r}).parent.mkdir(parents=True,exist_ok=True)
(b/'NMB_native').mkdir(exist_ok=True)
''');assert r.returncode==0,r.stderr
    r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
    (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
    r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});a={a!r}
names=[p for p in (b/a).rglob('*') if p.is_file() and 'sources' not in p.relative_to(b/a).parts]+[b/(a+'.json')]+[p for pat in ['-graph*','-source*','-lock*'] for p in b.glob(a+pat)]
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in names}}))
''');assert r.returncode==0,r.stderr
    out=json.loads(r.stdout)
    for n,t in out.items():
        p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
        if n.endswith('.log'):
            p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
        else:p.write_text(t)
    rc=json.loads(out[a+'/receipt.json'])
    # Evidence inputs are committed at their original content hashes once.
    idx=json.loads((E/'NMB_INPUTS.json').read_text())
    for n,t in files.items():
        if n==a+'.json':continue
        raw=t.encode();h=sha(raw);p=E/'NMB_INPUTS'/(h+'.xz')
        p.parent.mkdir(exist_ok=True)
        if not p.exists():p.write_bytes(lzma.compress(raw))
        idx['objects'][h]=dict(path=str(p.relative_to(E)),bytes=len(raw),archive_sha256=sha(p.read_bytes()));idx['attempts'].setdefault(a,{})[n]=h
    (E/'NMB_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
    summary={k:v for k,v in rc.items() if k!='deps_fingerprint'}
    summary['deps_fingerprint_ref']={'receipt':a+'/receipt.json','sha256':sha((E/a/'receipt.json').read_bytes())}
    with (E/'NMB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
    print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
    if rc['exit_status'] and kind=='lean':print(json.dumps(dict(attempt=a,error_excerpt=out[a+'/stdout.log'][-1500:])),flush=True)
    return rc
if __name__=='__main__':
    r=run(*sys.argv[1:]);sys.exit(r['exit_status'])

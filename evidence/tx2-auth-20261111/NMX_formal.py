"""Focused formal submissions through unchanged host launcher, one module per scope."""
from NMX_transport import *
import hashlib,re,shlex,sys,lzma
sha=lambda b:hashlib.sha256(b).hexdigest()
def _run(a,kind,target,command=None,extra=None,env_extra=None):
    assert ((a.startswith('NMX_L') and 1<=int(a[-3:])<=999) or (a.startswith('NMX_E') and 1<=int(a[-3:])<=2) or (a.startswith('NMX_K') and 1<=int(a[-3:])<=999)) and not (E/a).exists()
    assert kind in ['lean','link','audit','inspect','extract','kani']
    if kind in ['lean','link','audit','inspect']:
        done=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
        assert sum(x.get('kind') in ['lean','link','audit','inspect'] for x in done)<40,'Actual Lean compiler budget exhausted (40)'
        if target not in ['NMX_COMBINED_IMPORT','NMX_ProofDriver','NMX_ScanDriver']:
            assert sum(x.get('kind') in ['lean','link','audit','inspect'] for x in done)<38,'Reserve two final import/audit compiler slots'
    if kind=='kani':
        done=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
        excluded=set()
        assert sum(x['kind']=='kani' and x['attempt'] not in excluded for x in done)<10,'Actual cargo-kani budget exhausted'
    if kind=='extract':
        done=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
        assert sum(x.get('kind')=='extract' for x in done)<2
    env=json.loads((E/'NMX_ENV.json').read_text())
    env['TMPDIR']=B+'/NMX_tmp'
    env['CARGO_TARGET_DIR']=B+'/NMX_target'
    env['CARGO_NET_OFFLINE']='true'
    env.update(env_extra or {})
    files=dict(extra or {})
    if kind=='lean':
        text=(E/(target+'.lean')).read_text()
        for dep in re.findall(r'^import (NMX_[\w.]+)',text,re.M):
            h=sha((E/(dep+'.lean')).read_bytes())
            assert any(x.get('module')==dep and x['exit_status']==0 and h in x['source_hashes'].values() for x in [json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]),'Compile current direct import first: '+dep
        src='NMX_generated/'+target.replace('.','/')+'.lean';files[src]=text
        command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMX_generated','-o','NMX_objects/'+target.replace('.','/')+'.olean',src]
        if target in ['NMX_ProofDriver','NMX_ScanDriver']:command+=['-c','NMX_native/'+target+'.c']
    assert command
    cfg=dict(attempt=a,kind=kind,module=target,command=command,env=env,sources=list(files),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'selected_objects':{}},expected_time=('focused Lean elaboration' if kind=='lean' else 'optimized Rust compilation then CBMC verification of '+target if kind in ['kani','batch'] else 'optimized audit link' if kind=='link' else 'named raw axiom/module scan' if kind=='audit' else 'bounded source, metadata, export or hashing inspection'))
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
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']['selected_objects']=pins;(b/{(a+'.json')!r}).write_text(json.dumps(x,indent=1)+'\\n')
(b/'NMX_objects'/{target.replace('.','/')!r}).parent.mkdir(parents=True,exist_ok=True)
(b/'NMX_native').mkdir(exist_ok=True)
''');assert r.returncode==0,r.stderr
    r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
    raw=(r.stdout+r.stderr).encode();(E/(a+'-launcher.log.xz')).write_bytes(lzma.compress(raw));(E/(a+'-launcher.log.sha256')).write_text(sha(raw)+'\n')
    r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});a={a!r}
names=[p for p in (b/a).rglob('*') if p.is_file() and 'sources' not in p.relative_to(b/a).parts]+[b/(a+'.json')]+[p for pat in ['-graph*','-source*','-lock*'] for p in b.glob(a+pat)]
if {kind!r}=='audit':
 names += [p for p in (b/'NMX_audit'/{target!r}).rglob('*') if p.is_file()]
 names += [p for p in b.glob('NMX_LOADED_scan.jsonl') if p.is_file()]
 for p in (b/'NMX_audit'/{target!r}).glob('*.json'):
  for row in json.loads(p.read_text()).get('results',[]):
   q=b/('NEP_'+p.stem+'_'+row['root']+'_REACHABLE.txt')
   if q.is_file():names.append(q)
if {kind!r}=='extract':
 names += [p for p in (b/{target!r}).rglob('*') if p.is_file() and p.suffix not in ['.olean','.ir']]
if {kind!r}=='inspect':
 names += [b/n for n in ['NMX_TOOL_PINS.json','NMX_RETENTION.json','NMX_EXPORT.json','NMX_CLOSURE_PINS.json.xz','NMX_CLOSURE_PINS.json.sha256','NMX_UNUSED_POOL_FINDING.json'] if (b/n).is_file()]
out={{}}
for p in names:
 n=str(p.relative_to(b))
 if n.endswith('.xz'):
  import base64
  out[n+'.base64']=base64.b64encode(p.read_bytes()).decode()
 else:out[n]=p.read_text()
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
    out=json.loads(r.stdout)
    for n,t in out.items():
        p=E/('NMX_'+n if n.startswith('NEP_') else n);p.parent.mkdir(parents=True,exist_ok=True)
        if n.endswith('.base64'):
            import base64
            (E/n.removesuffix('.base64')).write_bytes(base64.b64decode(t))
        elif n.endswith('.log') or n.endswith('_REACHABLE.txt') or n.endswith('LOADED_scan.jsonl'):
            p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
        else:p.write_text(t)
    rc=json.loads(out[a+'/receipt.json'])
    # Evidence inputs are committed at their original content hashes once.
    idx=json.loads((E/'NMX_INPUTS.json').read_text())
    for n,t in files.items():
        if n==a+'.json':continue
        raw=t.encode();h=sha(raw);p=E/'NMX_INPUTS'/(h+'.xz')
        p.parent.mkdir(exist_ok=True)
        if not p.exists():p.write_bytes(lzma.compress(raw))
        idx['objects'][h]=dict(path=str(p.relative_to(E)),bytes=len(raw),archive_sha256=sha(p.read_bytes()));idx['attempts'].setdefault(a,{})[n]=h
    (E/'NMX_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
    summary={k:v for k,v in rc.items() if k!='deps_fingerprint'}
    summary.update(full_receipt=a+'/receipt.json',full_receipt_sha256=sha((E/a/'receipt.json').read_bytes()))
    with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
    print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
    if rc['exit_status'] and kind=='lean':print(json.dumps(dict(attempt=a,error_excerpt=out[a+'/stdout.log'][:1800])),flush=True)
    return rc
def run(*args,**kwargs):
    import os
    guard=E/'NMX_CLIENT_ACTIVE'
    fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY)
    os.write(fd,str(os.getpid()).encode());os.close(fd)
    try:return _run(*args,**kwargs)
    finally:guard.unlink()
if __name__=='__main__':
    r=run(*sys.argv[1:]);sys.exit(r['exit_status'])

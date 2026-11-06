"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx1-entry2-20261110';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NLQ_HOLD').exists():sys.exit(75)
guard=E/'NLQ_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NLQ_L[0-9]{3}',a) and 1<=int(a[-3:])<=140 and not (E/a).exists()
# Stricter owned-input validation: a dependent may not use a stale private object.
if kind=='lean':
 candidate=E/(target+'.lean')
 if not candidate.exists():candidate=E/'NLQ_dependency_inputs'/(target+'.lean.txt')
 receipts=[json.loads(line) for line in (E/'NLQ_ATTEMPTS.jsonl').read_text().splitlines()]
 for dep in re.findall(r'^import ((?:NLQ|NLM)_[\w.]+)',candidate.read_text(),re.M):
  source=E/(dep+'.lean')
  if not source.exists():source=E/'NLQ_dependency_inputs'/(dep+'.lean.txt')
  assert source.exists(), 'Missing pinned own dependency source: '+dep
  expected=hashlib.sha256(source.read_bytes()).hexdigest()
  assert any(r.get('module')==dep and r.get('exit_status')==0 and expected in r.get('source_hashes',{}).values() for r in receipts), 'Compile CURRENT dependency first: '+dep
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NLQ_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for disk_retry in range(7):
 disk=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage("+repr(B)+")._asdict()))")
 assert disk.returncode==0,disk.stderr
 disk_info=json.loads(disk.stdout)
 (E/(a+'-disk-'+str(disk_retry)+'.json')).write_text(json.dumps(disk_info))
 if disk_info['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP host free below40GB after six waits')
 for _ in range(10):time.sleep(60)
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r}; print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[]
if kind=='lean':
 if target=='NLQ_OwnerStatements':files['NLQ_AUDIT_ROOTS.json']=(E/'NLQ_AUDIT_ROOTS.json').read_text()
 n='NLQ_generated/'+target.replace('.','/')+'.lean';files[n]=((E/(target+'.lean'))if (E/(target+'.lean')).exists()else(E/'NLQ_dependency_inputs'/(target+'.lean.txt'))).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NLQ_generated','-o','NLQ_objects/'+target.replace('.','/')+'.olean',n]
 if target in ['NLQ_Driver','NLQ_ProofDriver','NLQ_PoolProofDriver','NLQ_PoolDriver']:command+=['-c','NLQ_native/'+target+'.c']
elif kind=='link':
 sources=['NLQ_native/'+target+'.c','NLQ_native/NFA_WALKER.c','NLQ_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLQ_native/'+target,*sources]
elif kind=='audit':
 if target=='retention':files['NLQ_retention.py']=(E/'NLQ_retention.py').read_text()
 if target in ['close','review-close']:
  files['NLQ_pin.py']=(E/'NLQ_pin.py').read_text();files['NLQ_PREDECESSOR_PINS.json']=lzma.decompress((E.parent/'ledger19-20261108/NKN_CLOSURE_PINS.json.xz').read_bytes()).decode()
 if target=='review-close':files['NLQ_generated/NLQ_HypothesisReview.lean']=(E/'NLQ_HypothesisReview.lean').read_text()
 sources=['NLQ_generated/NLQ_ProofDriver.lean','NLQ_generated/NLQ_Driver.lean','NLQ_batch.py','NLQ_AUDIT_ROOTS.json','NLQ_AUDIT_MODULES.json','NLQ_EXPECTED_IMPORTS.jsonl']+(['NLQ_POOL_ROOTS.json'] if target.startswith('pool') else [])+(['NLQ_pin.py','NLQ_PREDECESSOR_PINS.json']if target in ['close','review-close']else[])+(['NLQ_generated/NLQ_HypothesisReview.lean']if target=='review-close'else[])
 for n in sources:
  if n not in files:files[n]=(E/Path(n).name).read_text()
 if target=='retention':sources+=['NLQ_retention.py']
 command=['python3','NLQ_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLQ_tmp',CARGO_TARGET_DIR=B+'/NLQ_target',LEAN_PATH=':'.join([B+'/NLQ_objects']+json.loads((E/'NLQ_PATHS.json').read_text()))),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NLQ_native').mkdir(exist_ok=True);(b/'NLQ_objects').mkdir(exist_ok=True);(b/'NLQ_tmp').mkdir(exist_ok=True)
(b/'NLQ_objects'/{target.replace('.', '/')!r}).parent.mkdir(parents=True,exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b/'NLQ_native'/n
 if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed/'+n,p)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations']
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NLQ_COMBINED_IMPORT']
rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
rels.update(n.replace('.','/')+'.olean' for n in modules)
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NLQ_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NLQ_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NLQ_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NLQ_LOADED_scan.jsonl','NLQ_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
if {target!r}=='retention':names+=['NLQ_EXPORT.json','NLQ_TOOL_PINS.json']
out={{n:(b/n).read_text() for n in names}}
if {target!r} in ['close','review-close']:
 for n in ['NLQ_PREDECESSOR_COMPARISON.json','NLQ_EXPORT.json','NLQ_TOOL_PINS.json','NLQ_CLOSURE_PINS.json.sha256']:out[n]=(b/n).read_text()
 out['NLQ_CLOSURE_PINS.json.xz.hex']=(b/'NLQ_CLOSURE_PINS.json.xz').read_bytes().hex()
for name in ['NLQ_Driver','NLQ_ProofDriver','NLQ_PoolProofDriver','NLQ_PoolDriver']:
 p=b/'NLQ_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.xz.hex'):
  (E/n[:-4]).write_bytes(bytes.fromhex(t));continue
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NLQ_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NLQ_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6 if len(raw)>20_000_000 else 1))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NLQ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])

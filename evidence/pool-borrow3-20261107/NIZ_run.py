"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;I=E.parent/'pool-b3-20261106';H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-pool-borrow3-20261107';C='/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NIZ_ACTIVE.json').exists():raise SystemExit('own native/extraction scope active')
if (E/'NIZ_HOLD').exists():sys.exit(75)
guard=E/'NIZ_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert not (E/a).exists(), 'Attempt already has receipts; never overwrite';assert (re.fullmatch('NIZ_L[0-9]{3}',a) and 1<=int(a[-3:])<=60) or a in ['NIZ_M001','NIZ_E001'] and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NIZ_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
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
if kind=='diagnose':
 sources=['NIZ_diagnose.py'];files[sources[0]]=(E/sources[0]).read_text();command=['python3','NIZ_diagnose.py']
elif kind=='stage':
 sources=['NIZ_prepare_host.py','NIZ_INCLUDES.json','NIZ_KMX_copy_stubs.patch']
 for n in sources:files[n]=(E/n).read_text()
 command=['python3','NIZ_prepare_host.py']
elif kind=='lean':
 rel=target.replace('.','/');n='NIZ_generated/'+rel+'.lean';files[n]=(E/(rel+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NIZ_generated','-o','NIZ_objects/'+rel+'.olean',n]
 if target in ['NIZ_Driver','NIZ_ProofDriver','NIZ_PoolProofDriver','NIZ_PoolDriver']:command+=['-c','NIZ_native/'+target+'.c']
elif kind=='extract':
 sources=['NIZ_extract_host.py'];files['NIZ_extract_host.py']=(E/'NIZ_extract_host.py').read_text();command=['python3','NIZ_extract_host.py']
elif kind=='mir':
 sources=['NIZ_mir_host.py'];files['NIZ_mir_host.py']=(E/'NIZ_mir_host.py').read_text();command=['python3','NIZ_mir_host.py']
elif kind=='link':
 for wrapper in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  files['NIZ_native/'+wrapper]=(E.parent/'pool-b4-20261107/NIE_L011/sources/NIE_native'/wrapper).read_text()
 sources=['NIZ_native/'+target+'.c','NIZ_native/NFA_WALKER.c','NIZ_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NIZ_native/'+target,*sources]
elif kind=='audit':
 sources=['NIZ_generated/NIZ_ProofDriver.lean','NIZ_generated/NIZ_Driver.lean','NIZ_batch.py','NIZ_AUDIT_ROOTS.json']+(['NIZ_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 files['NIZ_EXPECTED_IMPORTS.jsonl']=(E/'NIZ_EXPECTED_IMPORTS.jsonl').read_text()
 command=['python3','NIZ_batch.py',target]
elif kind=='export':
 files['NIZ_export.py']=(E/'NIZ_export.py').read_text();sources=['NIZ_export.py'];command=['python3','NIZ_export.py']
elif kind=='cleanup':
 files['NIZ_cleanup.py']=(E/'NIZ_cleanup.py').read_text();sources=['NIZ_cleanup.py'];command=['python3','NIZ_cleanup.py']
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(CARGO_TARGET_DIR=B+'/NIZ_target',LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NIZ_tmp',LEAN_PATH=':'.join([B+'/NIZ_objects',C+'/NIO_exports_20261107',C+'/NIK_exports_20261107',C+'/NIE_exports_20261107',C+'/NHP_exports_20261106',C+'/NHP_native_exports_20261106',C+'/NHC_exports_20261105',C+'/NHC_native_exports_20261105',C+'/NHC_seed',C,W,W+'/objects',T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Optimized Rust compilation of the named uniqueness helper, then Charon/Aeneas translation' if kind=='extract' else 'Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Read/hash and non-destructive cache export; no compiler' if kind in ['export','cleanup'] else 'Raw ax2 traversal / coherence scan')
if kind=='lean':
 def own_closure(module, seen):
  p=E/(module.replace('.','/')+'.lean')
  if not p.exists():return
  for dep in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):
   if dep.startswith('NIZ_') and dep not in seen:
    seen.add(dep);own_closure(dep,seen)
 selected=set();own_closure(target,selected);config['own_transitive_modules']=sorted(selected)
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NIZ_objects'/{(target.replace('.','/'))!r}).parent.mkdir(parents=True,exist_ok=True)
(b/'NIZ_native').mkdir(exist_ok=True);(b/'NIZ_objects').mkdir(exist_ok=True);(b/'NIZ_tmp').mkdir(exist_ok=True)
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b/'NIZ_native'/name
 if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed/'+name,p)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations'] if x['kind']!='lean' or {target!r} in ['NIZ_Driver','NIZ_ProofDriver'] else []
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NIZ_COMBINED_IMPORT']
modules += x.get('own_transitive_modules',[])
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
x['deps_fingerprint']={{'large_input_hashes':{{'NIZ_EXPECTED_IMPORTS.jsonl':hashlib.sha256((b/'NIZ_EXPECTED_IMPORTS.jsonl').read_bytes()).hexdigest()}} if x['kind']=='audit' else {{}},'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NIZ_CACHE_IMPORTS.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='cleanup':names += ['NIZ_CLEANUP.json']
if {kind!r}=='export':names += ['NIZ_EXPORT.json','NIZ_CLOSURE_PINS.json.sha256']
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NIZ_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NIZ_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NIZ_LOADED_scan.jsonl','NIZ_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names}}
if {kind!r}=='export':
 import base64
 out['NIZ_CLOSURE_PINS.json.xz']=base64.b64encode((b/'NIZ_CLOSURE_PINS.json.xz').read_bytes()).decode()
for name in ['NIZ_Driver','NIZ_ProofDriver','NIZ_PoolProofDriver','NIZ_PoolDriver']:
 p=b/'NIZ_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n=='NIZ_CLOSURE_PINS.json.xz':
  import base64
  p.write_bytes(base64.b64decode(t,validate=True))
 elif n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NIZ_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NIZ_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NIZ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print('Full stdout and axiom lines retained in receipt directory.');sys.exit(rc['exit_status'])

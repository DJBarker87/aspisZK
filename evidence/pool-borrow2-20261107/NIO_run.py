"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;I=E.parent/'pool-b3-20261106';H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-pool-borrow2-20261107';C='/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NIO_ACTIVE.json').exists():raise SystemExit('own native/extraction scope active')
if (E/'NIO_HOLD').exists():sys.exit(75)
guard=E/'NIO_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert (re.fullmatch('NIO_L[0-9]{3}',a) and 1<=int(a[-3:])<=60) or a in ['NIO_M001','NIO_E001'] and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NIO_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
if kind=='lean':
 rel=target.replace('.','/');n='NIO_generated/'+rel+'.lean';files[n]=(E/(rel+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NIO_generated','-o','NIO_objects/'+rel+'.olean',n]
 if target in ['NIO_Driver','NIO_ProofDriver','NIO_PoolProofDriver','NIO_PoolDriver']:command+=['-c','NIO_native/'+target+'.c']
elif kind=='extract':
 sources=['NIO_extract_host.py'];files['NIO_extract_host.py']=(E/'NIO_extract_host.py').read_text();command=['python3','NIO_extract_host.py']
elif kind=='mir':
 sources=['NIO_mir_host.py'];files['NIO_mir_host.py']=(E/'NIO_mir_host.py').read_text();command=['python3','NIO_mir_host.py']
elif kind=='link':
 for wrapper in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  files['NIO_native/'+wrapper]=(E.parent/'pool-b4-20261107/NIE_L011/sources/NIE_native'/wrapper).read_text()
 sources=['NIO_native/'+target+'.c','NIO_native/NFA_WALKER.c','NIO_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NIO_native/'+target,*sources]
elif kind=='audit':
 sources=['NIO_generated/NIO_ProofDriver.lean','NIO_generated/NIO_Driver.lean','NIO_batch.py','NIO_AUDIT_ROOTS.json','NIO_EXPECTED_IMPORTS.jsonl']+(['NIO_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NIO_batch.py',target]
elif kind=='export':
 files['NIO_export.py']=(E/'NIO_export.py').read_text();sources=['NIO_export.py'];command=['python3','NIO_export.py']
elif kind=='cleanup':
 files['NIO_cleanup.py']=(E/'NIO_cleanup.py').read_text();sources=['NIO_cleanup.py'];command=['python3','NIO_cleanup.py']
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NIO_tmp',LEAN_PATH=':'.join([B+'/NIO_objects',C+'/NIK_exports_20261107',C+'/NIE_exports_20261107',C+'/NHP_exports_20261106',C+'/NHP_native_exports_20261106',C+'/NHC_exports_20261105',C+'/NHC_native_exports_20261105',C+'/NHC_seed',C,W,W+'/objects',T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Read/hash and non-destructive cache export; no compiler' if kind in ['export','cleanup'] else 'Raw ax2 traversal / coherence scan')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NIO_objects'/{(target.replace('.','/'))!r}).parent.mkdir(parents=True,exist_ok=True)
(b/'NIO_native').mkdir(exist_ok=True);(b/'NIO_objects').mkdir(exist_ok=True);(b/'NIO_tmp').mkdir(exist_ok=True)
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b/'NIO_native'/name
 if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed/'+name,p)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations'] if x['kind']!='lean' or {target!r} in ['NIO_Driver','NIO_ProofDriver'] else []
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NIO_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NIO_CACHE_IMPORTS.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NIO_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NIO_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NIO_LOADED_scan.jsonl','NIO_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names}}
for name in ['NIO_Driver','NIO_ProofDriver','NIO_PoolProofDriver','NIO_PoolDriver']:
 p=b/'NIO_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NIO_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NIO_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NIO_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print('Full stdout and axiom lines retained in receipt directory.');sys.exit(rc['exit_status'])

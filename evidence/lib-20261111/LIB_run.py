"""LIB-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-lib-20261111';C='/home/dombarker/project-offloads/codex-cx-lib-20261111';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'LIB_HOLD').exists():sys.exit(75)
guard=E/'LIB_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('LIB_L[0-9]{3}',a) and 1<=int(a[-3:])<=999 and not (E/a).exists()
assert int(a[-3:])<204 or sum(1 for z in E.glob('LIB_L[0-9][0-9][0-9]/receipt.json') if int(z.parent.name[-3:])>=204)<80
assert int(a[-3:])<182 or sum(1 for z in E.glob('LIB_L[0-9][0-9][0-9]/receipt.json') if int(z.parent.name[-3:])>=182)<162
assert int(a[-3:])<93 or sum(1 for z in E.glob('LIB_L[0-9][0-9][0-9]/receipt.json') if int(z.parent.name[-3:])>=93)<250
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'LIB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
while True:
 r=ssh('python3',"""import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):found.append(unit);break
print(json.dumps(dict(scopes=found,count=len(found))))
""")
 assert r.returncode==0,r.stderr
 share_info=json.loads(r.stdout)
 with (E/'LIB_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,event='share_check' if share_info['count']<6 else 'wait',reason='Stream A scope share',host=share_info))+'\n')
 if share_info['count']<6:break
 time.sleep(180)
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
  with (E/'LIB_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,event='wait',reason='reservation refusal',exit=r.returncode,reservation=ad))+'\n')
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[]
if kind=='lean':
 if target=='LIB_OwnerStatements':files['LIB_AUDIT_ROOTS.json']=(E/'LIB_AUDIT_ROOTS.json').read_text()
 n='LIB_generated/'+target.replace('.','/')+'.lean';files[n]=((E/(target+'.lean'))if (E/(target+'.lean')).exists()else(E/'LIB_dependency_inputs'/(target+'.lean'))).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','LIB_generated','-o','LIB_objects/'+target.replace('.','/')+'.olean',n]
 if target in ['LIB_Driver','LIB_ProofDriver','LIB_PoolProofDriver','LIB_PoolDriver']:command+=['-c','LIB_native/'+target+'.c']
elif kind=='audit':
 if target=='f9-pins':
  sources=['LIB_f9_pin.py','LIB_F9_SELECTED_MODULES.json','LIB_F9_SOURCE_PINS.json']
  command=['python3','LIB_f9_pin.py']
 elif target=='bundle-pins':
  sources=['LIB_bundle_pin.py','LIB_BUNDLE_SELECTED_MODULES.json','LIB_BUNDLE_SOURCE_PINS.json']
  command=['python3','LIB_bundle_pin.py']
 elif target=='pins':
  sources=['LIB_pin.py','LIB_SELECTED_MODULES.json','LIB_FINAL_SOURCE_PINS.json','LIB_AUDITOR_PIN.json','LIB_FINAL_AUDIT_SUMMARY.json']
  command=['python3','LIB_pin.py']
 else:
  sources=['LIB_audit.py','LIB_AUDIT_ROOTS.json','LIB_AUDIT_MODULES.json','LIB_AUDITOR_PIN.json','LIB_REUSED_AUDITOR_SOURCE.txt']
  command=['python3','LIB_audit.py',target]
 for n in sources:files[n]=(E/n).read_text()
else:raise ValueError('LIB runner supports one Lean module or one own-root audit per scope')
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/LIB_tmp',CARGO_TARGET_DIR=B+'/LIB_target',LEAN_PATH=':'.join([B+'/LIB_objects']+json.loads((E/'LIB_PATHS.json').read_text()))),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'LIB_native').mkdir(exist_ok=True);(b/'LIB_objects').mkdir(exist_ok=True);(b/'LIB_tmp').mkdir(exist_ok=True)
(b/'LIB_objects'/{target.replace('.', '/')!r}).parent.mkdir(parents=True,exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=['RSL_Base','RSL_Pool','RSL_Verifier']
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['LIB_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'LIB_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'LIB_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'LIB_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['LIB_LOADED_scan.jsonl','LIB_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names}}
if {target!r}=='f9-pins':
 for n in ['LIB_F9_EXPORT.json','LIB_F9_HOST.json','LIB_F9_CLOSURE_PINS.json.sha256']:
  out[n]=(b/n).read_text()
 out['LIB_F9_CLOSURE_PINS.json.xz.hex']=(b/'LIB_F9_CLOSURE_PINS.json.xz').read_bytes().hex()
if {target!r}=='bundle-pins':
 for n in ['LIB_BUNDLE_EXPORT.json','LIB_BUNDLE_HOST.json','LIB_BUNDLE_CLOSURE_PINS.json.sha256']:
  out[n]=(b/n).read_text()
 out['LIB_BUNDLE_CLOSURE_PINS.json.xz.hex']=(b/'LIB_BUNDLE_CLOSURE_PINS.json.xz').read_bytes().hex()
if {target!r}=='pins':
 for n in ['LIB_EXPORT.json','LIB_FINAL_HOST.json','LIB_CLOSURE_PINS.json.sha256']:
  out[n]=(b/n).read_text()
 out['LIB_CLOSURE_PINS.json.xz.hex']=(b/'LIB_CLOSURE_PINS.json.xz').read_bytes().hex()
if {target!r} in ['close','review-close','review-retention']:
 for n in ['LIB_PREDECESSOR_COMPARISON.json','LIB_EXPORT.json','LIB_TOOL_PINS.json','LIB_CLOSURE_PINS.json.sha256']:
  if (b/n).exists():out[n]=(b/n).read_text()
 if (b/'LIB_CLOSURE_PINS.json.xz').exists():out['LIB_CLOSURE_PINS.json.xz.hex']=(b/'LIB_CLOSURE_PINS.json.xz').read_bytes().hex()
if {target!r} in ['close','retention','review-retention']:
 if (b/'LIB_FINAL_HOST.json').exists():out['LIB_FINAL_HOST.json']=(b/'LIB_FINAL_HOST.json').read_text()
for name in ['LIB_Driver','LIB_ProofDriver','LIB_PoolProofDriver','LIB_PoolDriver']:
 p=b/'LIB_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.xz.hex'):
  (E/n[:-4]).write_bytes(bytes.fromhex(t));continue
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('LIB_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('LIB_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6 if len(raw)>20_000_000 else 1))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'LIB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])

"""NNW serial client; references frozen NNH objects and unchanged host launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re,os,atexit
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-rest-20261108'
C='/home/dombarker/project-offloads/codex-cx-integrate-20261111'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,target=sys.argv[1:]; assert re.fullmatch('NNW_L[0-9]{3}',a) and target.startswith('NNW_') and not (E/a).exists()
guard=E/'NNW_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def record(row):
 with (E/'NNW_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict({"attempt":a},**row))+'\n')
used={json.loads(l)['attempt'] for l in (E/'NNW_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(l).get('submitted')} if (E/'NNW_ATTEMPTS.jsonl').exists() else set()
assert len(used)<30

def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  if r.returncode!=255:return r
  record(dict(event='transport',retry=retry,exit=255,submitted=submitted,stderr=r.stderr))
  if submitted:raise RuntimeError('Submitted: recover read-only; never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
r=ssh('python3',f"from pathlib import Path;Path({B!r}).mkdir(exist_ok=True)"); assert r.returncode==0,r.stderr
for retry in range(11):
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
"""); assert r.returncode==0,r.stderr
  share=json.loads(r.stdout);record(dict(event='share_check' if share['count']<6 else 'wait',host=share))
  if share['count']<6:break
  time.sleep(180)
 for dr in range(7):
  r=ssh('python3',f'import shutil,json;print(json.dumps(shutil.disk_usage({B!r})._asdict()))');assert r.returncode==0,r.stderr
  disk=json.loads(r.stdout);(E/(a+f'-disk-{dr}.json')).write_text(r.stdout)
  if disk['free']>=40_000_000_000:break
  record(dict(event='wait',reason='disk below40GB',disk=disk))
  if dr==6:raise RuntimeError('Disk exhausted')
  
  for _ in range(10):time.sleep(60)
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''');(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  record(dict(event='wait',reason='reservation refusal',exit=r.returncode,reservation=ad));time.sleep(180);continue
 raise RuntimeError('STOP admission')
n='NNW_generated/'+target+'.lean';files={n:(E/(target+'.lean')).read_text()} if target!='NNW_RAW_AX2' else {n:(E/n).read_text() for n in ['NNW_audit.py','NNW_AUDIT_ROOTS.json','NNW_AUDIT_MODULES.json']}
roots=[B+'/NNW_objects']+json.loads((E/'NNW_PATHS.json').read_text())
cfg=dict(attempt=a,kind='lean',module=target,sources=[n],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNW_generated','-o','NNW_objects/'+target+'.olean',n],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NNW_tmp',LEAN_PATH=':'.join(roots)),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused proof elaboration and kernel checking')
if target=='NNW_RAW_AX2':
 cfg.update(kind='raw_ax2',sources=list(files),command=['python3','NNW_audit.py'],expected_time='Raw ax2 closure traversal of delivered RestLaw')
files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re
b=Path({B!r});c=Path({C!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for n in ['NNW_objects','NNW_tmp']:(b/n).mkdir(exist_ok=True)
# Byte-for-byte reuse, never modify the lead launcher.
s=c/'S2W_run_host.py';d=b/'S2W_run_host.py'
if d.exists():assert d.read_bytes()==s.read_bytes()
else:d.write_bytes(s.read_bytes())
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M) if x['kind']=='lean' else ['NNW_Rest']
rels=set(n.replace('.','/')+'.olean' for n in modules)
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins,'launcher_sha256':hashlib.sha256(s.read_bytes()).hexdigest(),'run6_cache_manifest_sha256':hashlib.sha256((c/'NNH_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
record(dict(event='submission',submitted=True,module=target))
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,lzma
b=Path({B!r});a={a!r};out={{str(p.relative_to(b)):p.read_text() for p in (b/a).rglob('*') if p.is_file()}};out[a+'.json']=(b/(a+'.json')).read_text()
p=b/'NNW_objects'/{(target+'.olean')!r}
if p.exists():out[a+'/NNW_PRODUCT.json']=json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
if {target!r}=='NNW_RAW_AX2':
 for p in (b/'NNW_audit_inputs').glob('NEP_*'):
  if p.is_file():
   raw=p.read_bytes();name=a+'/NNW_'+p.name
   if p.name.endswith('_REACHABLE.txt') or len(raw)>20_000_000:
    out[name+'.xz.hex']=lzma.compress(raw,preset=6).hex();out[name+'.sha256']=hashlib.sha256(raw).hexdigest()+'\\n'
   else:out[name]=raw.decode()
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/(n[:-4] if n.endswith('.xz.hex') else n);p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.xz.hex'):p.write_bytes(bytes.fromhex(t))
 else:p.write_text(t)
rc=json.loads((E/a/'receipt.json').read_text());record({k:v for k,v in rc.items() if k!='deps_fingerprint'})
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
sys.exit(rc['exit_status'])

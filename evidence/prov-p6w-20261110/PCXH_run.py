#!/usr/bin/env python3
"""PCXH serial client (derived from PCXF_run.py; changes recorded in PCXH_TOOLS.json): admission, upload, one capped systemd scope
running one or more Lean steps sequentially, collection, receipts.
Usage (from this directory, one scope at a time): python3 PCXH_run.py PCXH_L001 MOD1[,MOD2,...]   (MODi.lean next to this script)
Admission before EVERY launch: whole-host scope count < 6, Stream C (codex-pc-*) scopes < 5, free disk >= 45 GB (wait 10 min, 6 rechecks),
reservation barrier allowed:true exit 0 (55 GiB total). Caps: MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; 180 s timeout per Lean process.
LEAN_PATH: own exports, then the L187 replay closure (final/objs, objs, base_ref); no ledger30 chain; plain lean (no lake env)."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re,os,atexit,base64,lzma
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-pc-prov-p6w-20261110'
L187='/home/dombarker/project-offloads/codex-cx-replay-l187-20261109'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a=sys.argv[1];targets=sys.argv[2].split(',')
assert re.fullmatch('PCXH_L[0-9]{3}',a),'bad attempt id'
assert not (E/a).exists(),'attempt directory exists: never overwrite a receipt'
guard=E/'PCXH_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def event(x):
 with (E/'PCXH_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict({'attempt':a,'utc':time.time()},**x))+'\n')
def ssh(code,data=None,submitted=False,tmo=300):
 remote='timeout %d bash -c %s'%(tmo,shlex.quote(code))
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=20','-o','ServerAliveInterval=15',H,remote],input=data,capture_output=True,text=True)
  with (E/'PCXH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr[-300:]))+'\n')
  if r.returncode!=255:return r
  event(dict(event='wait',reason='transport',retry=retry,submitted=submitted))
  if retry<10:time.sleep(60)
 raise RuntimeError('STOP transport exhausted')
COUNT="""import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[];c=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except(FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):
   found.append(unit)
   if cwd.startswith('/home/dombarker/project-offloads/codex-pc-'):c.append(unit)
   break
print(json.dumps(dict(scopes=found,count=len(found),stream_c=c,stream_c_count=len(c))))
"""
for tries in range(40):
 r=ssh('python3',COUNT);assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);ok=x['count']<6 and x['stream_c_count']<5
 event(dict(event='share_check' if ok else 'wait',reason='host<6 and StreamC<5',host=x))
 if ok:break
 time.sleep(150)
else:raise RuntimeError('STOP share never below limit')
for retry in range(7):
 r=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage('/home/dombarker/project-offloads')._asdict()))");assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);(E/(a+f'-disk-{retry}.json')).write_text(r.stdout)
 if x['free']>=45_000_000_000:break
 event(dict(event='wait',reason='disk below 45GB',disk=x))
 if retry==6:raise RuntimeError('STOP disk below 45 GB after 6 rechecks')
 time.sleep(600)
ssh('mkdir -p '+shlex.quote(B))
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''');(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,allowed=ad.get('allowed'),reservation=ad),indent=2))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  event(dict(event='wait',reason='reservation refusal',exit=r.returncode));time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[];steps=[]
def put(name,path):files[name]=base64.b64encode(Path(path).read_bytes()).decode()
src_rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();dirty=bool(subprocess.check_output(['git','status','--porcelain','--','.'],text=True).strip())
imports=set()
for t in targets:
 assert (E/(t+'.lean')).exists(),t
 n='PCXH_sources/'+t+'.lean';put(n,E/(t+'.lean'));sources.append(n)
 imports.update(re.findall(r'^import ([\w.]+)',(E/(t+'.lean')).read_text(),re.M))
 steps.append(dict(module=t,source=n,olean=B+'/PCXH_exports/'+t+'.olean',command=[T+'/bin/lean','-j1','-M7000','-DElab.async=false','-DmaxErrors=100000','-R','PCXH_sources','-o','PCXH_exports/'+t+'.olean',n]))
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'};scope_p=['-p','MemoryHigh=6G','-p','MemoryMax=8G']
G='/home/dombarker/project-offloads/codex-pc-prov-p6v-20261110'  # PCXG exports, read-only by reference (unchanged modules only)
LP=':'.join([B+'/PCXH_exports',G+'/PCXG_exports',L187+'/final/objs',L187+'/objs',L187+'/base_ref'])
env=dict(LEAN_SYSROOT=T,PATH='/usr/bin:/bin',TMPDIR=B+'/PCXH_tmp',LEAN_PATH=LP)
config=dict(attempt=a,kind='lean',modules=targets,sources=sources,steps=steps,env=env,timeout=180,expected_limits=limits,source_revision=src_rev,source_tree_dirty=dirty,deps_fingerprint={},expected_time='Lean elaboration of generated equality bundles / deployed modules / audits, one process per module, in the L187 closure')
files[a+'.json']=base64.b64encode(json.dumps(config).encode()).decode()
files['PCXH_run_host.py']=base64.b64encode((E/'PCXH_run_host.py').read_bytes()).decode()
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,base64
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t))
for n in ['PCXH_exports','PCXH_sources','PCXH_tmp']:(b/n).mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text())
roots=x['env']['LEAN_PATH'].split(':');pins={{}}
for m in sorted({sorted(imports)!r}+['Aeneas']):
 rel=m.replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 if p is None:continue
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
event(dict(event='submission',targets=targets,caps=limits))
r=ssh('cd '+shlex.quote(B)+' && (nohup systemd-run --user --scope '+' '.join(scope_p)+' -p MemorySwapMax=0 -p TasksMax=64 python3 PCXH_run_host.py '+a+'.json > '+a+'-launcher.log 2>&1 < /dev/null &) ; sleep 1; echo launched',submitted=True,tmo=60)
assert 'launched' in r.stdout,r.stderr
t0=time.time()
while True:
 time.sleep(30)
 r=ssh('test -f '+shlex.quote(B+'/'+a+'/receipt.json')+' && echo DONE; test -d '+shlex.quote(B+'/'+a)+' || echo NODIR',submitted=True,tmo=60)
 if 'DONE' in r.stdout:break
 if time.time()-t0>3600:event(dict(event='long_wait'));
 if time.time()-t0>7200:raise RuntimeError('STOP poll exceeded 2 h; recover read-only')
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r});a={a!r};names=[p for p in (b/a).rglob('*') if p.is_file()]+[b/(a+'.json'),b/(a+'-launcher.log')]
for t in {targets!r}:
 p=b/'PCXH_exports'/(t+'.olean')
 if p.exists():
  q=b/(a+'-object-'+t+'.json');q.write_text(json.dumps(dict(module=t,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)));names.append(q)
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names}}))
''',tmo=300);assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
 raw=base64.b64decode(v);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if (len(raw)>1_000_000 or n.endswith(('stdout.log','time.log'))) and not n.endswith('.xz'):
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
assert (E/a/'receipt.json').exists(),'Missing receipt: never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k not in ('deps_fingerprint','env','steps')};entry['steps']=[{k:s[k] for k in ('module','exit_status','wall_seconds','peak_rss_kib','swaps','errors')} for s in rc['steps']];entry['full_receipt']=a+'/receipt.json';event(dict(event='result',**entry))
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])

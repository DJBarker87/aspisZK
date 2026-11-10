#!/usr/bin/env python3
"""NPL_ serial client (Stream A job NPL_, 2026-11-10): admission, upload, one capped systemd scope, collection, receipts.
Usage (from this directory, one scope at a time):  python3 -B NPL_run.py NPL_L001
One scope compiles NPL_PublicBytesRef.lean then NPL_PublicBytes.lean sequentially (-j1), inside one
systemd scope MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64, timeout 180 s for the whole command.
Derived from evidence/prov-p3l-20261110/PCVL_run.py (Stream C); changes: prefix, workspace, two sources,
admission = whole-host codex scope count < 6 AND host lean process count < 6, LEAN_PATH by reference to
the L187 replay base_ref (Aeneas/Mathlib closure) plus the pool-retarget cache for the gate module
(the object PCVJ_L003/PCVL_L007 pinned, sha 933f376d...)."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re,os,atexit,base64,lzma
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-pb-20261110'
GATE_T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
ROOTS=['/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/base_ref','/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104']
MODS=['NPL_PublicBytesRef','NPL_PublicBytes']
a=sys.argv[1]
assert re.fullmatch('NPL_L[0-9]{3}',a),'bad attempt id'
assert not (E/a).exists(),'attempt directory exists: never overwrite a receipt'
guard=E/'NPL_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def event(x):
 with (E/'NPL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict({'attempt':a,'utc':time.time()},**x))+'\n')
def ssh(code,data=None,submitted=False,tmo=300):
 remote='timeout %d bash -c %s'%(tmo,shlex.quote(code))
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=20','-o','ServerAliveInterval=15',H,remote],input=data,capture_output=True,text=True)
  with (E/'NPL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr[-500:]))+'\n')
  if r.returncode!=255:return r
  event(dict(event='wait',reason='transport',retry=retry,submitted=submitted))
  if submitted:raise RuntimeError('Submitted: recover read-only, NEVER resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('STOP transport exhausted')
# ---- (1)+(2) scope counts: whole host < 6 and Stream C (codex-pc-*) < 2
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
lean=int(subprocess.run(['pgrep','-c','-x','lean'],capture_output=True,text=True).stdout.strip() or 0)
print(json.dumps(dict(scopes=found,count=len(found),stream_c=c,stream_c_count=len(c),lean=lean)))
"""
for tries in range(30):
 r=ssh('python3',COUNT);assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);ok=x['count']<6 and x['lean']<6
 event(dict(event='share_check' if ok else 'wait',reason='host scopes<6 and lean<6',host=x))
 if ok:break
 time.sleep(180)
else:raise RuntimeError('STOP share never below limit')
# ---- (3) disk
for retry in range(7):
 r=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage('/home/dombarker/project-offloads')._asdict()))");assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);(E/(a+f'-disk-{retry}.json')).write_text(r.stdout)
 if x['free']>=40_000_000_000:break
 event(dict(event='wait',reason='disk below 40GB',disk=x))
 if retry==6:raise RuntimeError('STOP disk below 40 GB after 6 rechecks')
 time.sleep(600)
# ---- (4) reservation barrier
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
# ---- build config and upload set
files={};sources=[]
def put(name,path):files[name]=base64.b64encode(Path(path).read_bytes()).decode()
src_rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();dirty=bool(subprocess.check_output(['git','status','--porcelain','--','.'],text=True).strip())
for m in MODS:
 n='NPL_sources/'+m+'.lean';put(n,E/(m+'.lean'));sources.append(n)
L=GATE_T+'/bin/lake env lean -j1 -M7000 -DElab.async=false -DmaxErrors=100000 -R NPL_sources'
chain=' && '.join(f'{L} -o NPL_exports/{m}.olean NPL_sources/{m}.lean' for m in MODS)
command=['bash','-c',chain]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'};scope_p=['-p','MemoryHigh=6G','-p','MemoryMax=8G']
env=dict(LEAN_SYSROOT=GATE_T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NPL_tmp',LEAN_PATH=':'.join([B+'/NPL_exports']+ROOTS))
expected='Two focused import elaborations (transcription, then equality/length proofs); no aggregation'
config=dict(attempt=a,kind='lean',module='+'.join(MODS),sources=sources,command=command,env=env,timeout=180,expected_limits=limits,source_revision=src_rev,source_tree_dirty=dirty,deps_fingerprint={},expected_time=expected)
files[a+'.json']=base64.b64encode(json.dumps(config).encode()).decode()
files['NPL_run_host.py']=base64.b64encode((E/'NPL_run_host.py').read_bytes()).decode()
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil,base64
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t))
for n in ['NPL_exports','NPL_sources','NPL_tmp']:(b/n).mkdir(exist_ok=True)
for n in ['NPL_PublicBytesRef','NPL_PublicBytes']:
 for suf in ['.olean','.ilean','.olean.private','.olean.server','.ir']:(b/'NPL_exports'/(n+suf)).unlink(missing_ok=True)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not (b/n).exists():shutil.copy2(w/n,b/n)
x=json.loads((b/{(a+'.json')!r}).read_text())
roots=x['env']['LEAN_PATH'].split(':');pins={{}};rels=set()
for root in roots[1:]:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for s in x['sources']:
 rels.update(m.replace('.','/')+'.olean' for m in re.findall(r'^import ([\\w.]+)',(b/s).read_text(),re.M) if not m.startswith('NPL_'))
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots[1:] if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'resolved':str(z.resolve()),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
x['deps_fingerprint']={{'selected_objects':pins}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
event(dict(event='submission',kind='lean',target='+'.join(MODS),caps=limits))
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope '+' '.join(scope_p)+' -p MemorySwapMax=0 -p TasksMax=64 python3 NPL_run_host.py '+a+'.json',submitted=True,tmo=400)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# ---- collect
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r});a={a!r};names=[p for p in (b/a).rglob('*') if p.is_file()]+[b/(a+'.json')]
objs={{}}
for m in {MODS!r}:
 p=b/'NPL_exports'/(m+'.olean')
 if p.exists():objs[m]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
q=b/(a+'-object.json');q.write_text(json.dumps(objs));names.append(q)
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names}}))
''',tmo=300);assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
 raw=base64.b64decode(v);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if (len(raw)>1_000_000 or n.endswith(('stdout.log','time.log'))) and not n.endswith('.xz'):
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
assert (E/a/'receipt.json').exists(),'Missing receipt: never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k not in ('deps_fingerprint','env')};entry['full_receipt']=a+'/receipt.json';event(dict(event='result',**entry))
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));sys.exit(rc['exit_status'])

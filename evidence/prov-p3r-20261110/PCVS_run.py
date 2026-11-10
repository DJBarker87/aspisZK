#!/usr/bin/env python3
"""PCO serial client: admission, upload, one capped systemd scope, collection, receipts.

Usage (run from this directory, one scope at a time):
  python3 PCVS_run.py PCVS_E001 extract            # needs PCVS_E001_spec.json (render with PCVS_render_spec.py)
  python3 PCVS_run.py PCVS_L001 lean PRVEq_<M>     # needs PRVEq_<M>.lean next to this script
Pattern copied from evidence/ledger30-20261111/NNN_run.py and evidence/emission-repro-20261110/NMH_run.py.
Admission before EVERY launch: whole-host scope count < 6, Stream C (codex-pc-*) scopes < 2, free disk >= 40 GB
(wait 10 min, 6 times), reservation barrier allowed:true with exit 0 (55 GiB total). One scope at a time per job.
Caps: extraction MemoryHigh=3G MemoryMax=4G; Lean MemoryHigh=6G MemoryMax=8G; MemorySwapMax=0, TasksMax=64, timeout 180 s.
"""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,re,os,atexit,base64,lzma
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B=os.environ.get('PCVS_HOST_BASE','/home/dombarker/project-offloads/codex-pc-prov-p3r-20261110')  # each job sets its own host workspace
GATE_T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind=sys.argv[1:3];target=sys.argv[3] if len(sys.argv)>3 else None
assert re.fullmatch('PCVS_[EL][0-9]{3}',a) and kind in ('extract','lean'),'bad attempt id'
assert not (E/a).exists(),'attempt directory exists: never overwrite a receipt'
guard=E/'PCVS_CLIENT_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def event(x):
 with (E/'PCVS_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict({'attempt':a,'utc':time.time()},**x))+'\n')
def ssh(code,data=None,submitted=False,tmo=300):
 remote='timeout %d bash -c %s'%(tmo,shlex.quote(code))
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=20','-o','ServerAliveInterval=15',H,remote],input=data,capture_output=True,text=True)
  with (E/'PCVS_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr[-500:]))+'\n')
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
print(json.dumps(dict(scopes=found,count=len(found),stream_c=c,stream_c_count=len(c))))
"""
for tries in range(30):
 r=ssh('python3',COUNT);assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);ok=x['count']<6 and x['stream_c_count']<2
 event(dict(event='share_check' if ok else 'wait',reason='host<6 and StreamC<2',host=x))
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
def put(name,path,rename=None):files[rename or name]=base64.b64encode(Path(path).read_bytes()).decode()
src_rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();dirty=bool(subprocess.check_output(['git','status','--porcelain','--','.'],text=True).strip())
if kind=='extract':
 spec=json.loads((E/(a+'_spec.json')).read_text());assert spec['run']==a
 ES=E.parent
 stager=ES/'extract-stage-20261106/NHR_stage.py';pin=json.loads((E/'PCVS_STAGER_PIN.json').read_text());assert hashlib.sha256(stager.read_bytes()).hexdigest()==pin['sha256']
 man=ES/'emission-repro-20261110/NMH_STAGING_MANIFEST.json';pay=ES/'emission-repro-20261110/NMH_FROZEN_PAYLOAD.json.xz';psha=ES/'emission-repro-20261110/NMH_FROZEN_PAYLOAD.json.sha256'
 assert hashlib.sha256(lzma.decompress(pay.read_bytes())).hexdigest()==psha.read_text().strip()
 put('NHR_stage.py',stager);put('PCVS_STAGER_PIN.json',E/'PCVS_STAGER_PIN.json');put('NHR_STAGING_MANIFEST.json',man);put('NHR_FROZEN_PAYLOAD.json.xz',pay);put('NHR_FROZEN_PAYLOAD.json.sha256',psha)
 put('PCVS_extract.py',E/'PCVS_extract.py');put(a+'_spec.json',E/(a+'_spec.json'))
 sources=['PCVS_extract.py','NHR_stage.py','PCVS_STAGER_PIN.json','NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.sha256',a+'_spec.json']
 command=['python3','PCVS_extract.py',a];limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
 scope_p=['-p','MemoryHigh=3G','-p','MemoryMax=4G'];env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin');collect=[a+'_emitted','PCVS_TOOL_ATTEMPTS.jsonl']
 expected='Pinned optimized Charon extraction then one sequential Aeneas emission'
else:
 assert target and (E/(target+'.lean')).exists()
 n='PCVS_sources/'+target+'.lean';put(n,E/(target+'.lean'));sources=[n]
 L187='/home/dombarker/project-offloads/codex-cx-replay-l187-20261109'
 paths=[L187+'/final/objs',L187+'/objs',L187+'/base_ref','/home/dombarker/project-offloads/codex-pc-prov-p3h-20261110/PCVH_exports']
 command=[GATE_T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-DmaxErrors=100000','-R','PCVS_sources','-o','PCVS_exports/'+target+'.olean',n]
 limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'};scope_p=['-p','MemoryHigh=6G','-p','MemoryMax=8G']
 env=dict(LEAN_SYSROOT=GATE_T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/PCVS_tmp',LEAN_PATH=':'.join([B+'/PCVS_exports','/home/dombarker/project-offloads/codex-pc-prov-p3q-20261110/PCVQ_exports','/home/dombarker/project-offloads/codex-pc-prov-p3n-20261110/PCVN_exports','/home/dombarker/project-offloads/codex-pc-prov-p3l-20261110/PCVL_exports','/home/dombarker/project-offloads/codex-pc-prov-p3k-20261110/PCVK_exports']+paths));collect=[]
 expected='Focused import elaboration of one generated equality module'
config=dict(attempt=a,kind=kind,module=target or spec.get('spec_id'),sources=sources,command=command,env=env,timeout=180,expected_limits=limits,source_revision=src_rev,source_tree_dirty=dirty,deps_fingerprint={},expected_time=expected)
files[a+'.json']=base64.b64encode(json.dumps(config).encode()).decode()
files['PCVS_run_host.py']=base64.b64encode((E/'PCVS_run_host.py').read_bytes()).decode()
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil,base64
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t))
for n in ['PCVS_exports','PCVS_sources','PCVS_tmp']:(b/n).mkdir(exist_ok=True)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not (b/n).exists():shutil.copy2(w/n,b/n)
x=json.loads((b/{(a+'.json')!r}).read_text())
if x['kind']=='lean':
 roots=x['env']['LEAN_PATH'].split(':');pins={{}};rels=set()
 for root in roots:
  for stem in ['Aeneas','AeneasMeta']:
   p=Path(root)/stem
   if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
   if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
 rels.update(m.replace('.','/')+'.olean' for m in re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M))
 for rel in sorted(rels):
  p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
  for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
 x['deps_fingerprint']={{'selected_objects':pins}}
 (b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
event(dict(event='submission',kind=kind,target=target or spec['spec_id'],caps=limits))
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope '+' '.join(scope_p)+' -p MemorySwapMax=0 -p TasksMax=64 python3 PCVS_run_host.py '+a+'.json',submitted=True,tmo=400)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# ---- collect
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r});a={a!r};names=[p for p in (b/a).rglob('*') if p.is_file()]+[b/(a+'.json')]
for n in {collect!r}:
 p=b/n;names+=[q for q in p.rglob('*') if q.is_file()] if p.is_dir() else ([p] if p.exists() else [])
if {kind!r}=='lean':
 p=b/'PCVS_exports'/({target!r}+'.olean')
 if p.exists():
  q=b/(a+'-object.json');q.write_text(json.dumps(dict(module={target!r},path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)));names.append(q)
names=[p for p in names if p.suffix!='.llbc' and p.name not in ('metadata.json','metadata.stdout')]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names}}))
''',tmo=300);assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
 raw=base64.b64decode(v);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if (len(raw)>1_000_000 or n.endswith(('stdout.log','time.log','charon.time','aeneas.time','metadata.stderr'))) and not n.endswith('.xz'):
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
assert (E/a/'receipt.json').exists(),'Missing receipt: never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k not in ('deps_fingerprint','env')};entry['full_receipt']=a+'/receipt.json';event(dict(event='result',**entry))
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));sys.exit(rc['exit_status'])

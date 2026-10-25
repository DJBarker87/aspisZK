#!/usr/bin/env python3
"""Fixed owned extraction; sequential capped phases, no release adoption."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,time,signal,resource
W=Path(__file__).resolve().parent
BUILD=Path(json.loads((W/'plan.json').read_text()).get('build_directory',str(W)))
G=2**30;CAP=6*G;HIGH=4*G
UNIT='aspis-s126-claims-extract-20261025-r7'
def sha(p):
 with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(name,value):(W/name).write_text(json.dumps(value,indent=2)+'\n')
def inventory():
 root=Path('/sys/fs/cgroup');rows=[];size=0
 def read(p):
  nonlocal size
  with p.open('rb')as f:data=f.read(131073)
  assert len(data)<=131072
  size+=len(data);assert size<=8*2**20
  return data.decode().strip()
 def walk(p):
  assert len(rows)<8192
  row={'path':str(p.relative_to(root))}
  for n in ['cgroup.events','memory.max','memory.current','memory.swap.max']:
   if (p/n).exists():row[n]=read(p/n)
  rows.append(row)
  for q in sorted(p.iterdir()):
   if q.is_dir():assert not q.is_symlink();walk(q)
 walk(root)
 mem={}
 for line in read(Path('/proc/meminfo')).splitlines():
  k,v=line.split(':',1);words=v.split()
  if len(words)==2 and words[1]=='kB':mem[k]=int(words[0])*1024
 finite=[r for r in rows if 'populated 1' in r.get('cgroup.events','')and r.get('memory.max','max')!='max']
 reserved=sum(int(r['memory.max'])for r in finite)
 # Whole-host counters charge uncapped populations too. No subtraction,
 # process-name filtering or slab discount; overlaps deliberately overcharge.
 fields=['AnonPages','Shmem','Unevictable','Slab','KernelStack','PageTables','Dirty','Writeback']
 charge=sum(mem[k]for k in fields)
 own=any(r['path'].endswith(UNIT+'.scope')for r in finite)
 extra=0 if own else CAP
 limit=min(55*G,mem['MemTotal']-9*G)
 admitted=reserved+charge+extra<limit and mem['MemAvailable']>=CAP+9*G
 return dict(time=time.time(),groups=rows,memory=mem,finite_reserved_bytes=reserved,
  host_counter_fields=fields,host_counter_charge_bytes=charge,additional_bytes=extra,
  own_scope_included=own,limit_bytes=limit,admitted=admitted,
  qualification='Operational headroom check with whole-host counters and reserve; not a bound on arbitrary future uncapped growth.')
def source_pins():
 plan=json.loads((W/'plan.json').read_text());pins={}
 for row in plan['source_files']:
  p=BUILD/row['path'];assert p.is_file()and not p.is_symlink();h=sha(p);assert h==row['sha256'],str(p);pins[row['path']]=h
 return pins
def tool_pins():
 paths=[Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'),
 Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')]
 paths.append(paths[0].with_name('charon-driver'))
 for name in ['rustc','cargo']:
  q=subprocess.run(['/home/dombarker/.cargo/bin/rustup','which','--toolchain','nightly-2026-06-01',name],text=True,capture_output=True,timeout=15);assert q.returncode==0,q.stderr;paths.append(Path(q.stdout.strip()))
 runtime=set()
 for p in paths:
  q=subprocess.run(['/usr/bin/ldd',str(p)],text=True,capture_output=True,timeout=10,env={**os.environ,'LD_LIBRARY_PATH':str(paths[3].parent.parent/'lib')})
  assert 'not found' not in q.stdout,q.stdout
  for line in q.stdout.splitlines():
   for word in line.split():
    if word.startswith('/')and Path(word).is_file():runtime.add(Path(word))
 for p in (paths[3].parent.parent/'lib').glob('*.so*'):
  if p.is_file():runtime.add(p)
 assert len(runtime)<512
 return {str(p):sha(p)for p in paths+sorted(runtime)}
if '--inside' not in sys.argv:
 original_limit=resource.getrlimit(resource.RLIMIT_AS)
 resource.setrlimit(resource.RLIMIT_AS,(512*2**20,original_limit[1]));signal.alarm(40)
 before=inventory();save('admission-before-scope.json',before)
 if not before['admitted']:raise SystemExit('Fresh admission denied; no scope/compiler launched')
 signal.alarm(0);resource.setrlimit(resource.RLIMIT_AS,original_limit)
 cmd=['systemd-run','--user','--scope','--unit='+UNIT,'--property=MemoryHigh=4G','--property=MemoryMax=6G',
 '--property=MemorySwapMax=0','--property=RuntimeMaxSec=600',
 '--property=TasksMax=64','/usr/bin/python3','-I','-S','-B',str(W/'run.py'),'--inside']
 save('launch.json',dict(command=cmd,runner_sha256=sha(W/'run.py'),time=time.time(),address_limit_at_launch=resource.getrlimit(resource.RLIMIT_AS)))
 raise SystemExit(subprocess.call(cmd))
lock=Path('/tmp/aspis-s126-claims-extraction.lock.d')
try:lock.mkdir()
except FileExistsError:raise SystemExit('Existing host extraction lock; no tool launched')
(lock/'owner.json').write_text(json.dumps(dict(pid=os.getpid(),workspace=str(W))))
child=None
def stop_signal(n,_):raise SystemExit(128+n)
for sig in [signal.SIGTERM,signal.SIGHUP,signal.SIGINT]:signal.signal(sig,stop_signal)
try:
 cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
 assert (cg/'memory.max').read_text().strip()==str(CAP)
 assert (cg/'memory.high').read_text().strip()==str(HIGH)
 assert (cg/'memory.swap.max').read_text().strip()=='0'
 (cg/'memory.oom.group').write_text('1')
 assert (cg/'memory.oom.group').read_text().strip()=='1'
 sources=source_pins();tools=tool_pins();plan=json.loads((W/'plan.json').read_text())
 save('pins-before.json',dict(sources=sources,tools=tools,cgroup=str(cg),runner_sha256=sha(W/'run.py')))
 env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',
 CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(BUILD/'target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='',LD_LIBRARY_PATH=str(next(Path(p)for p in tools if Path(p).name=='rustc').parent.parent/'lib'))
 for key in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS']:env.pop(key,None)
 # New private target, only two local packages; no another-session cache writes.
 old=plan['host_directory'];commands=[[a.replace(old,str(W))for a in plan[k]]for k in ['charon_command','aeneas_command']]
 commands[0][commands[0].index('--manifest-path')+1]=str(BUILD/'reference/Cargo.toml')
 completed=[]
 for phase,cmd in zip(['charon','aeneas'],commands):
  inv=inventory();save(phase+'-admission.json',inv);assert inv['admitted']and inv['own_scope_included']
  if phase=='aeneas':
   llbc=json.loads((W/'ClaimsSafe.llbc').read_text());assert llbc.get('has_errors')is False,'Charon output is not error-free'
  (W/'generated').mkdir(exist_ok=True)
  timed=['/usr/bin/time','-v','-o',str(W/(phase+'-time.log')),'/usr/bin/timeout','--signal=TERM','--kill-after=5s','540s',*cmd]
  save(phase+'-input.json',dict(command=cmd,executed_command=timed,environment={k:env[k]for k in ['RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','RUSTFLAGS','LD_LIBRARY_PATH']},source_pins=sources,tool_pins=tools,expected_time='Focused optimized two-local-package extraction/translation; no certificates/SBF/SAT; stop after540s for review',print_axioms='N/A: source extraction, no theorem yet'))
  start=time.monotonic()
  with (W/(phase+'-stdout.log')).open('wb')as out,(W/(phase+'-stderr.log')).open('wb')as err:
   child=subprocess.Popen(timed,cwd=BUILD/'reference',env=env,stdout=out,stderr=err,start_new_session=True)
   status=child.wait();child=None
  record=dict(exit_status=status,wall_seconds=time.monotonic()-start,command=cmd,
   source_unchanged=source_pins()==sources,tools_unchanged=tool_pins()==tools,
   cgroup_values={k:(cg/k).read_text().strip()for k in ['memory.max','memory.high','memory.swap.max','memory.oom.group','memory.peak','memory.events']},
   print_axioms='N/A: source extraction only')
  save(phase+'-receipt.json',record);completed.append(phase)
  assert record['source_unchanged']and record['tools_unchanged']
  if status:break
 save('terminal.json',dict(completed=completed,time=time.time(),last_exit_status=status))
except BaseException as exc:
 save('terminal-error.json',dict(time=time.time(),error=repr(exc)))
 raise
finally:
 if child is not None and child.poll()is None:
  try:os.killpg(child.pid,signal.SIGTERM)
  except ProcessLookupError:pass
  try:child.wait(timeout=3)
  except subprocess.TimeoutExpired:
   try:os.killpg(child.pid,signal.SIGKILL)
   except ProcessLookupError:pass
   child.wait(timeout=3)
 if child is None or child.poll()is not None:
  (lock/'owner.json').unlink();lock.rmdir()

raise SystemExit(status)

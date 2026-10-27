#!/usr/bin/env python3
"""Future window monitor. No quiet-marker writes, no firmware or policy changes."""
import pathlib,subprocess,os,json,time,sys,signal
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027');O=pathlib.Path(sys.argv[1]);Q=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={x:(cg/x).read_text().strip() for x in ['memory.high','memory.max','memory.swap.max','pids.max']};assert list(limits.values())==['6442450944','8589934592','0','64']
policy_paths=['/sys/devices/system/cpu/cpu2/cpufreq/scaling_governor','/sys/devices/system/cpu/intel_pstate/no_turbo','/sys/devices/system/cpu/smt/active','/sys/devices/system/cpu/cpu2/topology/thread_siblings_list']
policy={p:pathlib.Path(p).read_text() for p in policy_paths}
marker=json.loads(Q.read_text());deadline=min(marker['until']-60,time.time()+600)
def guard():
 assert json.loads(Q.read_text())==marker,'window marker changed'
 assert time.time()<deadline,'sample deadline reached'
 assert all(pathlib.Path(p).read_text()==v for p,v in policy.items()),'CPU policy changed'
 for p in pathlib.Path('/sys/class/thermal').glob('thermal_zone*/temp'):
  assert int(p.read_text())<90000,'temperature >= 90 C'

 # Reject other finite-memory build scopes throughout the run, all users.
 for f in pathlib.Path('/sys/fs/cgroup/user.slice').rglob('memory.max'):
  p=f.parent
  if p==cg or p in cg.parents or cg in p.parents:continue
  try:
   if f.read_text().strip()!='max' and 'populated 1' in (p/'cgroup.events').read_text():raise RuntimeError('competing capped workload: '+str(p))
  except FileNotFoundError:continue
 events=dict(x.split() for x in (cg/'memory.events').read_text().splitlines())
 assert all(int(events[k])==0 for k in ['high','max','oom','oom_kill']),'memory cap pressure'
 # Catch uncapped compiler/prover jobs, excluding this timing process tree.
 for p in pathlib.Path('/proc').glob('[0-9]*/comm'):
  try:
   name=p.read_text().strip()
   if name in ['rustc','cargo','lean','lake','cc1','ld.lld','devnet_spend','kani-driver']:raise RuntimeError('competing process '+str(p)+': '+name)
  except (FileNotFoundError,PermissionError):continue
 return {'epoch':time.time(),'memory_current':(cg/'memory.current').read_text().strip(),'loadavg':pathlib.Path('/proc/loadavg').read_text().strip()}
rec=dict(artifacts=json.loads((B/'src/evidence/pv-l3-20261027/dudect/ready.json').read_text()),target=[str(B/'bin/pv-dudect'),'--measure','1000000'],kernel_cpu=2,monitor_cpu=0,policy=policy,limits=limits,print_axioms='N/A: no Lean',source_revision='73070ddd512bc4e79edfc0db714fb64dc74e87b8',DOITM='OFF: V371 retained',marker=marker,exit_status=None)
child=None;t=time.monotonic();reason=None
try:
 guard();subprocess.run(['python3',str(B/'src/tools/pv-dudect/metadata.py'),str(O)],check=True)
 with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se,(O/'monitor.jsonl').open('w') as mon:
  child=subprocess.Popen(['/usr/bin/time','-v','-o',str(O/'time.log'),'taskset','-c','2',*rec['target']],cwd=O,stdout=so,stderr=se,start_new_session=True)
  while child.poll() is None:
   mon.write(json.dumps(guard())+'\n');mon.flush();time.sleep(1)
  rec['exit_status']=child.returncode
except BaseException as e:
 reason=str(e)
 if child and child.poll() is None:
  os.killpg(child.pid,signal.SIGTERM)
  try:child.wait(timeout=5)
  except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
 rec['exit_status']=child.returncode if child else 78
finally:
 rec.update(abort_reason=reason,wall_seconds=time.monotonic()-t,peak_rss_scope_bytes=int((cg/'memory.peak').read_text()),swap_peak_bytes=int((cg/'memory.swap.peak').read_text()))
 (O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
sys.exit(0 if rec['exit_status']==0 and reason is None else 1)

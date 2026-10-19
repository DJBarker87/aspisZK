#!/usr/bin/env python3
"""Run ONE root-approved phase inside an already-capped exclusive scope."""
import argparse, datetime, fcntl, hashlib, json, os, signal, subprocess, time
from pathlib import Path
import host_gate as gate

p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--revision',required=True);p.add_argument('--phase',required=True);p.add_argument('--attempt',default='');p.add_argument('--gate',required=True);p.add_argument('--gate-ack-sha256',required=True);p.add_argument('--parallel-authorized',action='store_true');a=p.parse_args()
root=Path(a.root);evidence=Path(a.gate);prior=json.loads(evidence.read_text())
assert gate.sha(evidence)==a.gate_ack_sha256,'reviewed gate SHA differs'
assert prior['status']=='PASS' and prior['revision']==a.revision,'gate failed/revision mismatch'
assert prior.get('foreign_activity_allowed',False)==a.parallel_authorized,'parallel authorization must match reviewed gate'
assert time.time()-datetime.datetime.fromisoformat(prior['utc']).timestamp()<600,'gate older than10min; obtain fresh review'
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('::',1)[1].strip().lstrip('/')
assert (cg/'memory.max').read_text().strip()=='8589934592','wrong MemoryMax'
assert (cg/'memory.high').read_text().strip()=='6442450944','wrong MemoryHigh'
assert (cg/'memory.swap.max').read_text().strip()=='0','wrong MemorySwapMax'
plan=json.loads((root/'pipeline-plan.json').read_text())
phase=next((v for v in plan['phases'] if v['name']==a.phase),None)
if phase is None:
    phase=next((dict(v,name='replay-'+v['flow'],env=plan['replay_common_env']) for v in plan['replays'] if 'replay-'+v['flow']==a.phase),None)
assert phase is not None,'unknown phase'
run=root/'runs'/(a.phase+('-'+a.attempt if a.attempt else ''));run.mkdir(parents=True,exist_ok=False)
lock_path=gate.PARALLEL_LOCK if a.parallel_authorized else gate.LOCK
lock=open(lock_path,'a+');queued=time.time()
try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
except BlockingIOError:
    (run/'suppressed.json').write_text(json.dumps({'reason':'exclusive shared lock occupied','own_child_pid':None,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n');raise SystemExit(75)
pre=gate.assess(root,a.revision,locked=True,parallel_authorized=a.parallel_authorized)
(run/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
assert pre['status']=='PASS','launch preflight rejected; no child started'
env=dict(os.environ);env.update(phase.get('env',{}));env.pop('ASPIS_R16_READONLY_RUNTIME',None)
env={k:(a.revision if v=='FINAL_RECUT_REVISION' else v) for k,v in env.items()}
argv=phase['argv'];log=run/'stdout.log';timelog=run/'time.log';command=['/usr/bin/time','-v','-o',str(timelog),*argv]
(run/'command.json').write_text(json.dumps({'argv':command,'cwd':str(root/'source'),'phase_env':{k:env.get(k) for k in set(phase.get('env',{}))|{'CARGO_TARGET_DIR','RUSTUP_TOOLCHAIN','ASPIS_SOURCE_REVISION','ASPIS_R18_AFTER_REVISION'}},'revision':a.revision,'reviewed_gate_sha256':a.gate_ack_sha256,'lock_acquired_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'queue_seconds':time.time()-queued,'runner_sha256':gate.sha(__file__)},indent=2)+'\n')
start=time.monotonic();external=[];foreign_history={};reservation_changes=[];max_aggregate=0;stop_reason=None
with log.open('xb') as fd:
    child=subprocess.Popen(command,cwd=root/'source',env=env,stdout=fd,stderr=subprocess.STDOUT,start_new_session=True)
    while child.poll() is None:
        external=gate.activity(own_job=child.pid,own_cgroup=Path('/proc/self/cgroup').read_text().strip())
        for process in external:foreign_history[process['pid']]=process
        if external and not a.parallel_authorized:stop_reason='external proof/build arrived; stopped OWN child only'
        scopes=gate.reservations();aggregate=sum(v['max'] for v in scopes);max_aggregate=max(max_aggregate,aggregate)
        if not reservation_changes or reservation_changes[-1]['aggregate_max']!=aggregate:
            reservation_changes.append({'elapsed_seconds':time.monotonic()-start,'aggregate_max':aggregate,'scopes':scopes})
        if aggregate>=55*1024**3:stop_reason='aggregate scope caps unsafe; stopped OWN child only'
        available=next(int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
        if available<4*1024**3:stop_reason='less than4GiB OS/remote reserve; stopped OWN child only'
        if time.monotonic()-start>600:stop_reason='10min mandatory progress review; stopped OWN child, no cap raise'
        if stop_reason:
            os.killpg(child.pid,signal.SIGTERM)
            try:child.wait(timeout=3)
            except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
            break
        time.sleep(.25)
    code=child.wait()
elapsed=time.monotonic()-start
rawtime=timelog.read_text() if timelog.exists() else ''
def metric(name):
    for line in rawtime.splitlines():
        if name in line:return line.split(':',1)[1].strip()
    return None
receipt={'phase':a.phase,'exact_target':argv,'exit_status':code,'wall_seconds':elapsed,'peak_process_rss_kib':metric('Maximum resident set size'),'process_swaps':metric('Swaps'),'source_revision':a.revision,'cgroup':str(cg),'memory_max':int((cg/'memory.max').read_text()),'memory_high':int((cg/'memory.high').read_text()),'memory_swap_max':int((cg/'memory.swap.max').read_text()),'memory_swap_current':int((cg/'memory.swap.current').read_text()),'memory_peak':int((cg/'memory.peak').read_text()),'stop_reason':stop_reason,'external_arrivals':list(foreign_history.values()),'parallel_authorized':a.parallel_authorized,'user_authorization':gate.PARALLEL_AUTHORIZATION if a.parallel_authorized else None,'lock_path':lock_path,'max_aggregate_scope_caps':max_aggregate,'reservation_changes':reservation_changes,'reviewed_gate_sha256':a.gate_ack_sha256,'source_manifest_sha256':gate.sha(root/'source-files.json'),'stdout_sha256':gate.sha(log),'time_log_sha256':gate.sha(timelog) if timelog.exists() else None,'print_axioms':'not applicable: SBF/native/stack/CU phase, no formal theorem'}
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));raise SystemExit(code if code>=0 else 128-code)

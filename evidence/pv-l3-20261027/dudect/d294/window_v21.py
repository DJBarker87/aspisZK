#!/usr/bin/env python3
"""Future lead-run entrypoint. Reads an existing marker; NEVER creates/edits it.
Do not invoke during preparation. Host directory and binary hashes are pinned
in evidence/pv-l3-20261027/dudect/ready.json after static comparison.
"""
import pathlib,sys,json,time,subprocess,os,hashlib,signal,shutil
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027')
assert sys.argv[1:]==['--execute-lead-window'], 'lead must schedule the window first'
Q=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
marker=json.loads(Q.read_text());assert marker['until']-time.time()>=900,'need full 15-minute lead window'
ready=json.loads((B/'src/evidence/pv-l3-20261027/dudect/ready.json').read_text())
for name,h in ready['binary_sha256'].items():assert hashlib.sha256((B/'bin'/name).read_bytes()).hexdigest()==h
assert shutil.disk_usage(B).free>=2*1024**3,'need 2 GiB free for raw rows'
info=pathlib.Path('/proc/cpuinfo').read_text();assert all(x in info for x in ['rdtscp','constant_tsc','nonstop_tsc']),'TSC prerequisites missing'
fields=lambda text: {k.strip():v.strip() for k,v in (line.split(':',1) for line in text.split('\n\n')[0].splitlines() if ':' in line) if k.strip() in ['model name','cpu family','model','stepping','microcode']}
assert fields(info)==ready['cpu_identity'],'CPU identity changed: rebind before measurement'
assert all(pathlib.Path(p).read_text()==v for p,v in ready['cpu_policy'].items()),'CPU policy changed: rebind before measurement'
O=B/('window-'+str(int(time.time())));O.mkdir(exist_ok=False)
# Admission scanner is read-only. The only quiet-window exemption is the
# documented owner environment; this script requires the lead's existing marker.
with (O/'reservation.log').open('w') as log:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(O/'admission.json')],stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0 and json.loads((O/'admission.json').read_text())['allowed'] is True,'reservation refused; no scope started'
env=dict(os.environ,QUIET_WINDOW_OWNER='1')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','taskset','-c','0','python3',str(B/'d294/window_worker_v21.py'),str(O)]
with (O/'scope.log').open('w') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
print(O);sys.exit(r.returncode)

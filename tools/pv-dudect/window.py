#!/usr/bin/env python3
"""Future lead-run entrypoint. Reads an existing marker; NEVER creates/edits it.
Do not invoke during preparation. Host directory and binary hashes are pinned
in evidence/pv-l3-20261027/dudect/ready.json after static comparison.
"""
import pathlib,sys,json,time,subprocess,os,hashlib,signal
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027')
assert sys.argv[1:]==['--execute-lead-window'], 'lead must schedule the window first'
Q=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
marker=json.loads(Q.read_text());assert marker['until']-time.time()>=1800,'need full 30-minute lead window'
ready=json.loads((B/'src/evidence/pv-l3-20261027/dudect/ready.json').read_text())
for name,h in ready['binary_sha256'].items():assert hashlib.sha256((B/'bin'/name).read_bytes()).hexdigest()==h
O=B/('window-'+str(int(time.time())));O.mkdir(exist_ok=False)
# Admission scanner is read-only. The only quiet-window exemption is the
# documented owner environment; this script requires the lead's existing marker.
with (O/'reservation.log').open('w') as log:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(O/'admission.json')],stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'reservation refused; no scope started'
env=dict(os.environ,QUIET_WINDOW_OWNER='1')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','taskset','-c','0','python3',str(B/'src/tools/pv-dudect/window_worker.py'),str(O)]
with (O/'scope.log').open('w') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
print(O);sys.exit(r.returncode)

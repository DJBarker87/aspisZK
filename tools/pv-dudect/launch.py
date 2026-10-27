#!/usr/bin/env python3
"""Host-only admission; never writes a quiet marker; no timing except explicit dry stage."""
import pathlib,subprocess,sys,json,time
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027');stage=sys.argv[1]
assert stage.split('@')[0] in ['build-harness','build-candidate','dry','compare','metadata']
Q=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
assert not Q.exists() or time.time()>=json.loads(Q.read_text())['until'],'QUIET WINDOW HOLD'
with (B/(stage+'-reservation.log')).open('w') as log:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(B/(stage+'-admission.json'))],stdout=log,stderr=subprocess.STDOUT)
print((B/(stage+'-reservation.log')).read_text());sys.stdout.flush()
if r.returncode:sys.exit(r.returncode)
assert json.loads((B/(stage+'-admission.json')).read_text())['allowed'] is True, 'reservation denied'
sys.exit(subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'src/tools/pv-dudect/worker.py'),stage]).returncode)

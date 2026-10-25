#!/usr/bin/env python3
"""One dependent source-changed job after the existing claim queue terminates."""
from pathlib import Path
import json,time,subprocess,sys
W=Path(__file__).resolve().parent;record=W/'field-queue.json'
assert not record.exists()
prior=W.parent/'native-prepared-claim-halves-20261025-v6/remaining-queue.json'
start=time.monotonic();record.write_text(json.dumps(dict(state='waiting_for_claim_queue',time=time.time()))+'\n')
while True:
 state=json.loads(prior.read_text())['state']
 if state in ['complete','stopped_on_failure_or_admission']:break
 if time.monotonic()-start>1400:
  record.write_text(json.dumps(dict(state='observation_timeout_no_restart',time=time.time()))+'\n');raise SystemExit(2)
 time.sleep(2)
record.write_text(json.dumps(dict(state='running',time=time.time()))+'\n')
status=subprocess.call([sys.executable,'-I','-S','-B',str(W/'nuc.py'),'point6'])
record.write_text(json.dumps(dict(state='terminal',exit_status=status,time=time.time()))+'\n')
raise SystemExit(status)

#!/usr/bin/env python3
"""Continue only after the existing hi4 job terminates successfully; never restart it."""
from pathlib import Path
import json,sys,time,subprocess
W=Path(__file__).resolve().parent
record=W/'remaining-queue.json'
assert not record.exists()
def save(**kw):record.write_text(json.dumps(kw,indent=2)+'\n')
start=time.monotonic();prior=W/'run-hi4/outer-terminal.json'
save(state='waiting_for_existing_hi4',started=time.time())
while not prior.exists():
 if time.monotonic()-start>610:
  save(state='observation_timeout_no_restart',time=time.time());raise SystemExit(2)
 time.sleep(2)
assert json.loads(prior.read_text())['exit_status']==0, 'hi4 did not pass; no next job launched'
for case in ['lo5','hi5']:
 assert not (W/('run-'+case)).exists()
 save(state='running',case=case,time=time.time())
 status=subprocess.call([sys.executable,'-I','-S','-B',str(W/'nuc.py'),case])
 if status:
  save(state='stopped_on_failure_or_admission',case=case,exit_status=status,time=time.time());raise SystemExit(status)
save(state='complete',exit_status=0,time=time.time())

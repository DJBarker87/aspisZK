#!/usr/bin/env python3
"""Sequential new current-source checks, never restart the existing source-old check."""
from pathlib import Path
import sys,time,json,subprocess
W=Path(__file__).resolve().parent;record=W/'queue-state.json';assert not record.exists()
prior=W.parent/'native-prepared-field-20261025-v2/run-point5/outer-terminal.json'
start=time.monotonic();record.write_text(json.dumps(dict(state='waiting_for_existing_field_point5',time=time.time()))+'\n')
while not prior.exists():
 if time.monotonic()-start>610:raise SystemExit('Observation timeout; no restart or new job')
 time.sleep(2)
for case in ['point5','point6']:
 assert not (W/('run-'+case)).exists()
 record.write_text(json.dumps(dict(state='running',case=case,time=time.time()))+'\n')
 status=subprocess.call([sys.executable,'-I','-S','-B',str(W/'nuc.py'),case])
 if status:
  record.write_text(json.dumps(dict(state='stopped',case=case,exit_status=status,time=time.time()))+'\n');raise SystemExit(status)
record.write_text(json.dumps(dict(state='complete',exit_status=0,time=time.time()))+'\n')

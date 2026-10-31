#!/usr/bin/env python3
"""Admission/transport retries for the lane-owned source preparation only."""
from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
for retry in range(11):
 r=subprocess.run(['python3',str(E/'NEB_setup.py')],capture_output=True,text=True)
 log=(E/'NEB_SETUP.log').read_text() if (E/'NEB_SETUP.log').exists() else ''
 (E/(f'NEB_SETUP-retry-{retry}.log')).write_text(r.stdout+r.stderr+'\n'+log)
 if r.returncode==0:print(r.stdout);break
 if '"allowed": false' in log or "'allowed': False" in log:
  if retry<10:print('source setup admission refused; wait three minutes',flush=True);time.sleep(180);continue
 if 'returncode=255' in log or 'Connection closed' in log or 'Connection reset' in log:
  if retry<10:print('prelaunch transport; wait sixty seconds',flush=True);time.sleep(60);continue
 raise SystemExit('Source preparation failed; no prover launch: '+(r.stdout+r.stderr+log)[-1800:])
else:raise SystemExit('source preparation admission/transport retries exhausted')

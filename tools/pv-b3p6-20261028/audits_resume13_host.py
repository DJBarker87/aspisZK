"""Run the three reserved audit IDs once, in order, using current admission."""
from pathlib import Path
import subprocess,time
def invoke(cmd):
 for retry in range(11):
  p=H/"admission-not-before.json"
  while p.exists() and (remaining:=json.loads(p.read_text())["epoch"]-time.time())>0:time.sleep(min(30,remaining))
  r=subprocess.run(cmd,cwd=H).returncode
  if r!=78:return r
 return 78
import sys
from run import H
import json
for m in ['PV_B3P_Resume13Combined','PV_B3P_Resume13Axioms','PV_B3P_Resume13Focused']:
 t=json.loads((H/'TALLY-resume13.json').read_text());assert t['lean_attempts']>=97
 if any(r['module']==m for r in t['receipts']):raise SystemExit('Audit already charged; recover its receipt instead of repeating it')
 r=invoke(['python3','compile_resume13.py',m,'audit'])
 if r:raise SystemExit(r)

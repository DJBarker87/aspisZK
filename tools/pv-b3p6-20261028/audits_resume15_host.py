from pathlib import Path
import subprocess,sys,json,time
from run import H
for module in ['PV_B3P_Resume15Combined','PV_B3P_Resume15Axioms','PV_B3P_Resume15Focused']:
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists() and (remaining:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,remaining))
  result=subprocess.run(['python3','compile_resume15.py',module,'audit'],cwd=H)
  if result.returncode==78:continue
  if result.returncode:raise SystemExit(result.returncode)
  break
 else:raise SystemExit(78)

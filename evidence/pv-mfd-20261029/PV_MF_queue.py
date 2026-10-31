from pathlib import Path
import json,subprocess,time
D=Path(__file__).resolve().parent
jobs=[('rebuild',m) for m in json.load(open(D/'rebuild-frontier-input.json'))['modules']]+[('check','V243')]
for n,(mode,m) in enumerate(jobs,70000):
 for retry in range(11):
  r=subprocess.run(['python3',str(D/'PV_MF_rebuild_host.py'),mode,m,str(n)])
  if r.returncode!=78:break
  print('REFUSAL',n,retry,flush=True);time.sleep(181)
 if r.returncode:raise SystemExit(r.returncode)

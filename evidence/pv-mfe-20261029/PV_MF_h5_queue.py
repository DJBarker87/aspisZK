from pathlib import Path
import json,subprocess,time,sys
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');jobs=json.load(open(D/sys.argv[1]));n=int(sys.argv[2]);charged=0
for mode,m in jobs:
 for retry in range(11):
  assert n<=70399
  assert len(list(D.glob('lean-*/result.json')))<80
  r=subprocess.run(['python3',str(D/'PV_MF_h5_host.py'),mode,m,str(n)])
  n+=1
  if r.returncode!=78:break
  print('REFUSAL',n-1,retry,flush=True);time.sleep(181)
 if r.returncode:raise SystemExit(r.returncode)
 print('NEXT',n,flush=True)

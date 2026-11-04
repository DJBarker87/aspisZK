from pathlib import Path
import json,subprocess,time
D=Path(__file__).resolve().parent
assert json.load(open(D/'lean-70030/result.json'))['exit']==0
(D/'rebuild-input.json').write_bytes((D/'next-input.json').read_bytes())
for n,(mode,m) in enumerate(json.load(open(D/'next-jobs.json'))[:69],70031):
 for retry in range(11):
  r=subprocess.run(['python3',str(D/'PV_MF_rebuild_host.py'),mode,m,str(n)])
  if r.returncode!=78:break
  print('REFUSAL',n,retry,flush=True);time.sleep(181)
 if r.returncode:raise SystemExit(r.returncode)

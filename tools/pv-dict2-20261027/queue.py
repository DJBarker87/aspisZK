from pathlib import Path
import json,subprocess,time,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dict2-20261027';queue=json.loads((E/'recheck-queue.json').read_text())
# The first admission was refused before scope launch at 13:55:06 UTC.
if sys.argv[1:] == ['cooldown']:time.sleep(180)
for m in queue:
 t=json.loads((E/'TALLY.json').read_text())
 if any(x['module']==m and x.get('exit')==0 for x in t['attempts']):continue
 if t['lean_charged']>=59:break
 for retry in range(11):
  t=json.loads((E/'TALLY.json').read_text());n=t['next_env_j_id']
  if n>=54897:raise SystemExit('ID space reserved for audit')
  status=subprocess.run(['python3',str(R/'tools/pv-dict2-20261027/lean.py'),str(n),m]).returncode
  if status==0:break
  if status==78 and retry<10:
   print('reservation refused; cooldown 180 seconds; next unused ID',flush=True);time.sleep(180);continue
  raise SystemExit(status)
print('queue checkpoint',json.loads((E/'TALLY.json').read_text())['lean_charged'],flush=True)

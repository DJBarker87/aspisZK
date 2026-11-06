from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for pair in json.loads((E/'NIX_MORE_PLAN.json').read_text()):
 for role in ['positive','negative']:
  a=pair[role]
  with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
  p=E/a/'receipt.json'
  if not p.exists():print(a,'NO RECEIPT STOP',flush=True);raise SystemExit(1)
  rc=json.loads(p.read_text());s=(E/a/'stdout.log').read_text();print(a,rc['exit_status'],rc['wall_seconds'],flush=True)
  if 'could not compile' in s or 'graph_matches_frozen' in s:print('STOP compile/graph finding',flush=True);raise SystemExit(1)
  if role=='positive' and 'VERIFICATION:- SUCCESSFUL' not in s:print('Park isolated stage; continue independent unit; control remains unsubmitted',flush=True);break
  if role=='negative' and ('VERIFICATION:- FAILED' not in s or 'unwinding failures' in s):print('STOP control encoding failure',flush=True);raise SystemExit(1)

# Per-job invocation wrapper; the shared launcher and reservation policy stay unchanged.
from pathlib import Path
import subprocess,json,time,sys
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');start=int(sys.argv[1]);budget=60
for retry in range(11):
 tally=json.loads((D/'TALLY.json').read_text()) if (D/'TALLY.json').exists() else {'receipts':[],'next_unused_id':start}
 held=json.loads((D/'NEXT-ID.json').read_text()) if (D/'NEXT-ID.json').exists() else {'next_unused_id':start}
 nextid=max(start,tally['next_unused_id'],held['next_unused_id']);completed={x['module'] for x in tally['receipts']}
 rows=json.loads((D/'rows.json').read_text());index=next((i for i,r in enumerate(rows) if r['module'] not in completed),len(rows))
 if index==len(rows):break
 r=subprocess.run(['python3',str(D/'compile.py'),str(nextid),str(budget),str(index)])
 new=json.loads((D/'TALLY.json').read_text()) if (D/'TALLY.json').exists() else tally
 if len(new['receipts'])>len(tally['receipts']):
  if new['receipts'][-1]['exit']:break
  if all(r['module'] in {x['module'] for x in new['receipts']} for r in rows):break
 used=sorted(int(x.name) for x in (D/'lean-receipts').iterdir());last=D/'lean-receipts'/str(used[-1]);log=(last/'reservation.log').read_text()
 wait=30 if 'FileNotFoundError' in log else 180
 print('admission wait',wait,'seconds; retry',retry+1,flush=True)
 if retry==10:break
 for _ in range(wait//30):time.sleep(30)

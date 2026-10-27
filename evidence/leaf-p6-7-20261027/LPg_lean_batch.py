from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
rows=[('lean','LPg_Geometry')]+[('inherited',r['module']) for r in json.loads((E/'LPg_inherited-plan.json').read_text())]
for i,(kind,m) in enumerate(rows,1):
 a=f'LPg_L{i:03}'
 if (E/a/'receipt.json').exists():
  if json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP previous failure '+a)
  continue
 subprocess.run(['python3',str(E/'LPg_attempt.py'),a,kind,m],check=True)
 if json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP '+a+' '+m)

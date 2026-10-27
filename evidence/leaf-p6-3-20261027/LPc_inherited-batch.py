from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
subprocess.run(['python3',str(E/'LPc_attempt.py'),'LPc_L001','lean','LPc_Iteration'],check=True)
if json.loads((E/'LPc_L001/receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP generic predecessor')
for i,row in enumerate(json.loads((E/'LPc_inherited-plan.json').read_text()),2):
 a=f'LPc_L{i:03}'
 subprocess.run(['python3',str(E/'LPc_attempt.py'),a,'inherited',row['module']],check=True)
 r=json.loads((E/a/'receipt.json').read_text())
 if r['exit_status']!=0:raise SystemExit('STOP failed prerequisite '+a)

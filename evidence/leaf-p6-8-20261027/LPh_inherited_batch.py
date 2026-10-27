from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for i,r in enumerate(json.loads((E/'LPh_inherited-plan.json').read_text()),18):
 a=f'LPh_L{i:03}'
 subprocess.run(['python3',str(E/'LPh_attempt.py'),a,'inherited',r['module']],check=True,stdout=(E/(a+'-summary.log')).open('w'),stderr=subprocess.STDOUT)
 receipt=json.loads((E/a/'receipt.json').read_text());print(a,r['module'],receipt['exit_status'],flush=True)
 if receipt['exit_status']:raise SystemExit('STOP missing or failed prerequisite '+a)

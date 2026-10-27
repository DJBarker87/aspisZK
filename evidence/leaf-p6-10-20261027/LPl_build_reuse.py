from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for i,row in enumerate(json.loads((E/'LPl_transform.json').read_text()),2):
 a=f'LPl_L{i:03}'
 subprocess.run(['python3',str(E/'LPl_attempt.py'),a,'lean',row['module']],check=True,stdout=(E/(a+'-summary.log')).open('w'),stderr=subprocess.STDOUT)
 r=json.loads((E/a/'receipt.json').read_text());print(a,row['module'],r['exit_status'],flush=True)
 if r['exit_status']:raise SystemExit('STOP failed prerequisite')

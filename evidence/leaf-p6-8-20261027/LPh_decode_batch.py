from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for i,lo in [(14,16),(15,22),(16,74),(17,80)]:
 a=f'LPh_K{i:03}';t=f'r1_wire::LPh_wire::LPh_decode_class{lo}'
 subprocess.run(['python3',str(E/'LPh_attempt.py'),a,'kani',t],check=True,stdout=(E/(a+'-summary.log')).open('w'),stderr=subprocess.STDOUT)
 r=json.loads((E/a/'receipt.json').read_text());print(a,r['exit_status'],r['wall_seconds'],flush=True)
 if r['exit_status']:raise SystemExit('STOP new failure '+a)

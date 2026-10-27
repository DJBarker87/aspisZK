from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;D='fast_pairing::canonical::LPg_dot::LPg_'
rows=['half_reject','scalar_reject','qsub_contract','qhalf_contract','product_contract','finish_canonical','dot_witness']
for i,name in enumerate(rows,24):
 a=f'LPg_K{i:03}'
 subprocess.run(['python3',str(E/'LPg_attempt.py'),a,'kani',D+name],check=True)
 r=json.loads((E/a/'receipt.json').read_text())
 if r['exit_status']!=0:raise SystemExit('STOP new failure '+a)

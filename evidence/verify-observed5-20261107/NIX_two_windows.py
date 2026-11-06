from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a in ['NIX_K045','NIX_K046']:
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'NO RECEIPT STOP',flush=True);break
 x=json.loads(p.read_text());print(a,x['exit_status'],x['wall_seconds'],flush=True)
 # The second unit is an independent assertion cut, never a replay of the first.

from pathlib import Path
import subprocess,json,sys
from NIH_config import write
E=Path(__file__).resolve().parent
jobs=[(63,'NIH_atpoint',False),(64,'NIH_atpoint',True),(65,'NIH_boxed_atpoint',False),(66,'NIH_boxed_atpoint',True)]
for n,name,negative in jobs:
 a=f'NIH_K{n:03}';write(a,'kani','pool_v1::pair_forest_copy_terminal::NIH_native::'+name,'--cfg NIH_invert' if negative else '')
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt STOP',flush=True);sys.exit(1)
 rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text();expected=r.returncode==(1 if negative else 0) and ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in raw
 print(json.dumps(dict(attempt=a,negative=negative,exit=r.returncode,expected=expected,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'])),flush=True)
 if not expected:sys.exit(1)

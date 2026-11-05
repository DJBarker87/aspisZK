from pathlib import Path
import subprocess,json,sys
from NIH_config import write
E=Path(__file__).resolve().parent
jobs=[(32,'NDE_matrix_cell',True),(33,'NDE_scan_cell',False),(34,'NDE_scan_cell',True),(35,'NDE_packed_after',False),(36,'NDE_packed_after',True)]
for n,name,negative in jobs:
 a=f'NIH_K{n:03}';write(a,'kani','state_only_poseidon::NDE_native::'+name,'--cfg NIH_invert' if negative else '')
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt STOP',flush=True);sys.exit(1)
 rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text();expected=r.returncode==(1 if negative else 0) and ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in raw
 print(json.dumps(dict(attempt=a,negative=negative,exit=r.returncode,expected=expected,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'])),flush=True)
 if not expected:sys.exit(1)

from pathlib import Path
import subprocess,json,sys
from NIH_config import write
E=Path(__file__).resolve().parent
jobs=[(53,'NIH_native::NIH_raw_extension',False),(54,'NIH_native::NIH_raw_extension',True),(55,'NIH_internal_native::NIH_internal_acc',False),(56,'NIH_internal_native::NIH_internal_acc',True),(57,'NIH_internal_native::NIH_internal_full',False),(58,'NIH_internal_native::NIH_internal_full',True),(59,'NIH_internal_native::NIH_internal_zero',False),(60,'NIH_internal_native::NIH_internal_zero',True),(61,'NIH_internal_native::NIH_internal_lane',False),(62,'NIH_internal_native::NIH_internal_lane',True)]
for n,name,negative in jobs:
 a=f'NIH_K{n:03}';write(a,'kani','state_only_poseidon::'+name,'--cfg NIH_invert' if negative else '')
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt STOP',flush=True);sys.exit(1)
 rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text();expected=r.returncode==(1 if negative else 0) and ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in raw
 print(json.dumps(dict(attempt=a,negative=negative,exit=r.returncode,expected=expected,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'])),flush=True)
 if not expected:sys.exit(1)

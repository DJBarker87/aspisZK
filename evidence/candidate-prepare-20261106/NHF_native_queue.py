"""Serial independent cuts; inspect solver verdict and stop a failed shape."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[('NHF_K007','heap_split',False),('NHF_K008','heap_split',True),('NHF_K009','semantic_stage',False),('NHF_K010','semantic_stage',True),('NHF_K011','values_stage',False),('NHF_K012','values_stage',True)]
for a,name,bad in jobs:
 env=dict(os.environ)
 if bad:env['NHF_BAD_STAGE']='1'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NHF_run.py'),a,'kani','verifier::candidate::NHF_stages::'+name],stdout=f,stderr=subprocess.STDOUT,env=env)
 text=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 expected=('VERIFICATION:- FAILED' in text and 'Failed Checks: assertion failed' in text) if bad else 'VERIFICATION:- SUCCESSFUL' in text
 print(json.dumps(dict(attempt=a,exit=r.returncode,expected_verdict=expected)),flush=True)
 if not expected or 'timed out' in text.lower():raise SystemExit('STOP shape; inspect/split before proceeding')

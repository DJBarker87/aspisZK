"""Serial proof queue; stop on every unexpected verdict or missing receipt."""
from pathlib import Path
import subprocess,json,os,sys
E=Path(__file__).resolve().parent
jobs=json.loads(sys.argv[1])
for a,kind,target,negative in jobs:
 env=dict(os.environ)
 if negative:env['NGT_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGT_run.py'),a,kind,target],env=env,capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if not (E/a/'receipt.json').exists():raise RuntimeError('Recover transport/input failure before continuing: '+a)
 x=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text()
 expected=('VERIFICATION:- FAILED' in s if negative else 'VERIFICATION:- SUCCESSFUL' in s) if kind=='kani' else x['exit_status']==0
 print(a,x['exit_status'],expected,flush=True)
 if not expected:print(s[-3500:],flush=True);break

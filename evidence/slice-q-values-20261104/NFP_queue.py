"""Own serial queue. Stop on any unexpected verdict, including timeout."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,kind,target,expected in json.loads(sys.argv[1]):
 with (E/(a+'-client.log')).open('w') as out:
  r=subprocess.run([sys.executable,str(E/'NFP_run.py'),a,kind,target],stdout=out,stderr=subprocess.STDOUT)
 print(a,target,r.returncode,flush=True)
 if r.returncode!=expected:print((E/(a+'-client.log')).read_text()[-1800:],flush=True)
 if r.returncode!=expected:raise SystemExit(r.returncode or 99)
 if kind=='kani':
  log=(E/a/'stdout.log').read_text();needle='VERIFICATION:- SUCCESSFUL' if expected==0 else 'VERIFICATION:- FAILED'
  assert needle in log,'Unexpected non-verdict; review before any next scope'

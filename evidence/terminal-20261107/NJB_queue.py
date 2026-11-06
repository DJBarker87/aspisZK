"""Serial owned-input queue; unchanged shared launcher/admission remains authoritative."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for arg in sys.argv[1:]:
 a,_,expected=arg.partition(':');expected=int(expected or '0')
 r=subprocess.run([sys.executable,str(E/'NJB_run.py'),a])
 if r.returncode!=expected:sys.exit(r.returncode or 79)
 if expected:
  log=(E/a/'stdout.log').read_text()
  if 'VERIFICATION:- FAILED'not in log or 'timed out'in log.lower() or 'error[E'in log or ('unwinding assertion' in log.lower() and 'FAILURE' in log):sys.exit(79)
print('serial queue complete',flush=True)

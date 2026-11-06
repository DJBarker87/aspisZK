"""Serial owned batches stop on timeout, memory failure or compilation failure."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).parent
for a in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(E/'NJA_run.py'),a])
 p=E/a/'stdout.log'
 if not p.exists():raise SystemExit('NJA batch stopped: missing terminal log')
 text=p.read_text()
 if any(s in text for s in ['CBMC timed out','excessive memory consumption','out of memory','could not compile','error: Failed to execute cargo']):
  raise SystemExit('NJA batch stopped: review '+a)
 if 'VERIFICATION:- SUCCESSFUL' not in text and 'VERIFICATION:- FAILED' not in text:
  raise SystemExit('NJA batch stopped: no semantic verdict '+a)
 if r.returncode not in (0,1):raise SystemExit(r.returncode)

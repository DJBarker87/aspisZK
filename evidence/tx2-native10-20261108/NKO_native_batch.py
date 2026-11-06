"""Own serial batch: distinct focused windows; matched controls; no retries."""
from pathlib import Path
import json,subprocess,sys,re
E=Path(__file__).resolve().parent
plan=json.loads((E/sys.argv[1]).read_text())
for row in plan:
 p,c,target=row
 if (E/p/'receipt.json').exists():raise RuntimeError('Existing attempt; recover, never resubmit')
 r=subprocess.run([sys.executable,str(E/'NKO_run.py'),p,'kani',target])
 if r.returncode==0:
  subprocess.run([sys.executable,str(E/'NKO_pair.py'),p,c,target])
 else:
  with (E/'NKO_FAILING_STEP.md').open('a')as f:f.write(f'\n{p}: {target} did not pass; {c} NOT launched. Retain exact log and isolate rather than rerun unchanged.\n')
  break

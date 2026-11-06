"""Run the two final serial scopes, then package the concrete gate result."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[['NJO_run.py','NJO_L039','lean','NJO_HypothesisReview'],['NJO_run.py','NJO_L040','audit','close'],['NJO_finalize.py'],['NJO_package.py'],['NJO_validate.py'],['NJO_handoff.py']]
for job in jobs:
 r=subprocess.run([sys.executable,str(E/job[0]),*job[1:]],capture_output=True,text=True)
 print(json.dumps(dict(job=job,exit=r.returncode,summary=r.stdout[-800:],error=r.stderr[-1200:])),flush=True)
 if r.returncode:sys.exit(r.returncode)

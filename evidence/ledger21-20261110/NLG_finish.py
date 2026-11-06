"""Local completion only after all forty authorized scopes have receipts."""
from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
while not(E/'NLG_L040/receipt.json').exists()or(E/'NLG_CLIENT_ACTIVE').exists():time.sleep(3)
assert json.loads((E/'NLG_L040/receipt.json').read_text())['exit_status']==0
# These are owned disposable Python bytecode outputs, not task keys or host cache.
for p in(E/'__pycache__').glob('*.pyc'):p.unlink()
if(E/'__pycache__').exists()and not list((E/'__pycache__').iterdir()):(E/'__pycache__').rmdir()
for name in ['NLG_finalize.py','NLG_hygiene.py','NLG_retention.py','NLG_validate.py']:
 start=time.monotonic();r=subprocess.run([sys.executable,'-B',str(E/name)],capture_output=True,text=True)
 row=dict(validation=name,exit=r.returncode,wall_seconds=time.monotonic()-start,stdout=r.stdout,stderr=r.stderr,scope=False)
 with(E/'NLG_FINAL_CHECKS.jsonl').open('a')as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(dict(validation=name,exit=r.returncode,summary=r.stdout[-700:],error=r.stderr[-1000:])),flush=True)
 if r.returncode:sys.exit(r.returncode)

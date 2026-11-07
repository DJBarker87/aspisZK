"""Serial owned source queue; stop on a rejected module, never resubmit a receipt."""
from pathlib import Path
import json,subprocess,sys,time
E=Path(__file__).resolve().parent
x=json.loads((E/sys.argv[1]).read_text())
if x.get('after'):
 p=E/x['after']/'receipt.json'
 while not p.exists():time.sleep(1)
 assert json.loads(p.read_text())['exit_status']==0
while (E/'NNG_CLIENT_ACTIVE').exists():time.sleep(1)
for a,m in x['targets']:
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run([sys.executable,str(E/'NNG_compile.py'),a,m])
 if r.returncode:raise SystemExit(r.returncode)

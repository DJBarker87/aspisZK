"""Own serial dependency replay after the cut pre-state correction."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
schedule=json.loads((E/sys.argv[1]).read_text())
for attempt,target in schedule:
 p=E/attempt/'receipt.json'
 if p.exists():
  assert json.loads(p.read_text())['exit_status']==0,('failed prior attempt; assign a new changed-source attempt',attempt)
  continue
 r=subprocess.run([sys.executable,str(E/'NIT_run.py'),attempt,'lean',target])
 if r.returncode:sys.exit(r.returncode)

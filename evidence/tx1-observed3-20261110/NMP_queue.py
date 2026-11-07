"""Sequential own client queue; a submitted attempt is never resubmitted."""
from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
prerequisite=sys.argv[1]
while not (E/prerequisite/'receipt.json').exists():time.sleep(5)
assert json.loads((E/prerequisite/'receipt.json').read_text())['exit_status']==0
while (E/'NMP_CLIENT_ACTIVE').exists():time.sleep(1)
for a in sys.argv[2:]:
 assert not (E/a/'receipt.json').exists(),('Never resubmit',a)
 r=subprocess.run([sys.executable,str(E/'NMP_run.py'),a])
 if r.returncode:sys.exit(r.returncode)

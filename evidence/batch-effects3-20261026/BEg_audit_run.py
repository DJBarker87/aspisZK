"""Serial task inventory, through the unchanged capped host launcher."""
from pathlib import Path
import json,subprocess
P=Path(__file__).resolve().parent
for row in json.loads((P/'BEg_source_audit_plan.json').read_text()):
 n=row['attempt']; module=row['module']
 result=subprocess.run(['python3',str(P/'BEg_compile.py'),str(n),module],capture_output=True,text=True)
 print(n,module,result.returncode,flush=True)
 if result.returncode:
  print(result.stdout[-5000:]+result.stderr[-2000:],flush=True)
  raise SystemExit(result.returncode)

"""Serial own-root batches; each child independently admits one capped scope."""
from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parent
for i,_ in enumerate(json.loads((p/'NNC_AUDIT_ROOTS.json').read_text())['groups']):
 r=subprocess.run([sys.executable,str(p/'NNC_audit.py'),f'NNC_L{45+i:03d}','audit','batch'+str(i)])
 if r.returncode:sys.exit(r.returncode)

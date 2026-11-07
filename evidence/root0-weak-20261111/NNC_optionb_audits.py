"""Only appended option-B roots, one admission/capped scope at a time."""
from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parent
start=int(sys.argv[1])
for offset,index in enumerate(range(8,len(json.loads((p/'NNC_AUDIT_ROOTS.json').read_text())['groups']))):
 r=subprocess.run([sys.executable,str(p/'NNC_audit.py'),f'NNC_L{start+offset:03d}','audit','batch'+str(index)])
 if r.returncode:sys.exit(r.returncode)

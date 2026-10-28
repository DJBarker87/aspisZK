from pathlib import Path
import subprocess,sys,json
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
for kind,op in [('forest',132),('forest',133),('forest',228),('copies',222),('copies',224),('copies',226)]:
 print(json.dumps(dict(start=op,kind=kind)),flush=True)
 r=subprocess.run(['python3',str(H/('extract_forest.py' if kind=='forest' else 'extract_copies.py')),str(op),'b3b02'])
 print(json.dumps(dict(op=op,exit=r.returncode)),flush=True)
 if r.returncode==78:sys.exit(78)
 if r.returncode not in [0,1,2,124]:sys.exit(r.returncode)

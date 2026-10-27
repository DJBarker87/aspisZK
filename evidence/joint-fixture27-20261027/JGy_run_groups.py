"""Sequential task targets; each invokes the existing capped host runner."""
from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent
rows=json.loads((P/'JGy_GROUPS.json').read_text())
start=int(sys.argv[1]) if len(sys.argv)>1 else 13
for i,row in enumerate(rows,start):
 print('BEGIN',i,row['module'],flush=True)
 r=subprocess.run([sys.executable,str(P/'JGy_compile.py'),str(i),row['module']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print('END',i,'exit',r.returncode,r.stdout[-800:],flush=True)
 if r.returncode:sys.exit(r.returncode)

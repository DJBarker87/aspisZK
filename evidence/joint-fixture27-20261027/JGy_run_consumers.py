"""Sequential consumer checks in topological order, reusing checked objects."""
from pathlib import Path
import subprocess,json,sys
P=Path(__file__).resolve().parent
start=int(sys.argv[1]);assert start+23<=100
for n,row in enumerate(json.loads((P/'JGy_CONSUMERS.json').read_text()),start):
 print('BEGIN',n,row['module'],flush=True)
 r=subprocess.run([sys.executable,str(P/'JGy_compile.py'),str(n),row['module']],capture_output=True,text=True)
 print('END',n,'exit',r.returncode,(r.stdout+r.stderr)[-1600:],flush=True)
 if r.returncode:sys.exit(r.returncode)

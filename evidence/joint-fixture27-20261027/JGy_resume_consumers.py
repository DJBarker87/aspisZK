"""Check only current-hash unchecked consumers, stopping at the fixed budget."""
from pathlib import Path
import subprocess,json,sys,hashlib
P=Path(__file__).resolve().parent; R=P.parents[1]
valid={(s,h) for f in P.glob('JGy27_*/receipt.json') for r in [json.loads(f.read_text())] if r['exit_status']==0 for s,h in r['source_hashes'].items()}
n=int(sys.argv[1])
for row in json.loads((P/'JGy_CONSUMERS.json').read_text()):
 m=row['module'];h=hashlib.sha256((R/'lean'/f'{m}.lean').read_bytes()).hexdigest()
 if (m+'.lean',h) in valid:continue
 if n>99:print('Reserved100 for separate top audit; stop consumer budget',flush=True);sys.exit(99)
 print('BEGIN',n,m,flush=True)
 r=subprocess.run([sys.executable,str(P/'JGy_compile.py'),str(n),m],capture_output=True,text=True)
 print('END',n,'exit',r.returncode,(r.stdout+r.stderr)[-1600:],flush=True)
 if r.returncode:sys.exit(r.returncode)
 n+=1
print('NEXT_ATTEMPT',n,flush=True)

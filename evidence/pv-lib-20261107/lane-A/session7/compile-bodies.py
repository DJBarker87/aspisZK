"""Serial focused compilation of the checked source-bound syntax bodies."""
from pathlib import Path
import hashlib,json,subprocess,sys
E=Path('evidence/pv-lib-20261107/lane-A/session7')
rows=[r for r in json.loads((E/'EMITTED_BODIES.json').read_text())['functions']if'module'in r]
for a,r in enumerate(rows,47439):
 p=r['source'];assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==r['sha256']
 subprocess.run(['git','add',p],check=True)
 q=subprocess.run([sys.executable,str(E.parent/'compile-s7.py'),str(a),r['module']])
 if q.returncode:sys.exit(q.returncode)
 h=E.parent/'HANDOFF.md';h.write_text(h.read_text()+f'\n{a} passed {r["module"]}. Exact emitted syntax only; no native adequacy or row closure.\n')
 subprocess.run(['git','add',str(h),str(E)],check=True)
 subprocess.run(['git','commit','--only',p,str(h),str(E),'-m','Retain checked emitted body '+str(r['function'])],check=True)

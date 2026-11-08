"""Serial post-build scan and frozen pre-split raw groups; stop on any failure."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
# Resume only after L053 is recovered; do not repeat submitted work.
jobs=[(54+i,'batch'+str(44+i))for i in range(7)]
assert jobs[-1][0]==60
assert len(json.loads((E/'NNM_AUDIT_ROOTS.json').read_text())['groups'])==51
for n,target in jobs:
 r=subprocess.run([sys.executable,str(E/'NNM_run.py'),f'NNM_L{n:03}','audit',target])
 if r.returncode:sys.exit(r.returncode)

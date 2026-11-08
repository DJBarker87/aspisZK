"""Serial post-build scan and frozen pre-split raw groups; stop on any failure."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
ranges=[(0,1),(2,4),(5,7)]+[(i,i+1)for i in range(8,58,2)]
jobs=[(31,'scan')]+[(32+i,f'batch{a}-{b}')for i,(a,b)in enumerate(ranges)]+[(60,'retention')]
assert len(ranges)==28
assert len(json.loads((E/'NNM_AUDIT_ROOTS.json').read_text())['groups'])==58
for n,target in jobs:
 r=subprocess.run([sys.executable,str(E/'NNM_run.py'),f'NNM_L{n:03}','audit',target])
 if r.returncode:sys.exit(r.returncode)

"""Fail-closed preflight for the small hand-bound iterator modules.
No generated numeral reduction or imported XR model is permitted.
"""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdcd4-20261029'
rows=[]
for p in sorted(L.glob('PV_RDCD4_*.lean')):
 s=p.read_text()
 forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|^import\s+\S*XR|set_option\s+(?:maxHeartbeats|maxRecDepth)',s,re.M)
 assert not forbidden,(p,forbidden)
 rows.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),prints=re.findall(r'^#print axioms (\S+)',s,re.M),large_reduction='none; list/iterator states remain symbolic'))
(E/'proof-preflight.json').write_text(json.dumps(dict(modules=rows,revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),scope='Source preflight only; successful kernel receipts required separately'),indent=2)+'\n')
print('Preflight:',len(rows),'new symbolic modules; forbidden constructs absent')

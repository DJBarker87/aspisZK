"""Derive private-name symbolic proof modules. Never copy to an existing module path."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent;L=R/'docs/research/v8-r0-zk-20261009/lean'
missing=json.loads((E/'missing-interpolation.json').read_text())
rename={n.split('.')[-1]:'PV_Inv_I'+n.split('.')[-1].replace('ProverCommit','').replace('48','') for n in missing}
manifest=[];order=[]
def visit(n):
 if n in order:return
 for d in missing[n]['deps']:
  if d in missing:visit(d)
 order.append(n)
visit('R1Z.ProverCommitInterpolationInitial48')
for n in order:
 p=R/missing[n]['path'];s=p.read_text();original=hashlib.sha256(s.encode()).hexdigest()
 for old,new in rename.items():s=s.replace(old,new)
 s=s.replace('/-!', '/-! Derived into private PV_Inv module names for this focused proof; original theorem bodies retained. ' ,1)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b',s)
 q=L/'R1Z'/(rename[n.split('.')[-1]]+'.lean');assert not q.exists();q.write_text(s)
 manifest.append(dict(original_module=n,original_path=str(p.relative_to(R)),original_sha256=original,new_module='R1Z.'+q.stem,new_source_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='module/namespace references and explanatory comment only; no shared existing source overwritten'))
(E/'derived-interpolation.json').write_text(json.dumps(manifest,indent=2)+'\n');print(' '.join(m['new_module'].split('.')[-1].replace('PV_Inv_','') for m in manifest))

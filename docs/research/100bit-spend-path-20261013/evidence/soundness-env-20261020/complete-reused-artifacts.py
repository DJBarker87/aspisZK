"""Complete the retained J object bundles without overwriting any J file.
Run once after discovering Lean 4.32's split object and IR requirements.
"""
from pathlib import Path
import json,shutil,hashlib
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
records=json.loads((J/'evidence-S/reused-receipts.json').read_text());out=[]
for module in records:
 p=J/'objects'/(module.replace('.','/')+'.olean')
 for src in p.parent.glob(p.stem+'.*'):
  if src.name==p.name:continue
  dst=J/'objects-S'/src.relative_to(J/'objects')
  shutil.copy2(src,dst)
  out.append({'module':module,'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'size':src.stat().st_size})
(J/'evidence-S/reused-artifacts.json').write_text(json.dumps(out,indent=2)+'\n')
print('retained artifacts',len(out))

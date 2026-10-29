from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');rows=[]
for root in [D/'external-objects',D/'rdcd/objects',D/'rdeac/objects']:
 for p in root.rglob('*.olean'):
  if not p.is_symlink():continue
  original=p.resolve()
  for suffix in ['.server','.private']:
   source=Path(str(original)+suffix);target=Path(str(p)+suffix)
   if source.is_file():
    if not target.exists():target.symlink_to(source)
    rows.append(dict(path=str(target),authority_object=str(original),source=str(source),sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
(D/'companion-inputs.json').write_text(json.dumps(rows,indent=2)+'\n');print('linked',len(rows),'original Lean companion inputs')

from pathlib import Path
import json,hashlib,shutil
w=Path('/home/dombarker/project-offloads/s5-stage2-dot-accumulator-v1-20261020');c=json.loads((w/'config.json').read_text());pre=w/'prebuilt';roots=[Path(x) for x in c['lean_path']];records=[]
for ns in sorted(p.name for p in pre.iterdir() if p.is_dir()):
 for root in roots:
  d=root/ns
  if d==pre/ns or not d.is_dir():continue
  for src in sorted(d.rglob('*')):
   if not src.is_file() or src.suffix not in ['.olean','.ilean','.ir','.private','.server']:continue
   dst=pre/src.relative_to(root)
   if dst.exists():continue
   dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy(src,dst);records.append({'destination':str(dst),'owner':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()})
(w/'namespace-coalescence.json').write_text(json.dumps(records,indent=2)+'\n');print('filled',len(records))

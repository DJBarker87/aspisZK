from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-dict2-20261027');B=D.parent;e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[B/'aspis-joint-20261019/objects']+[Path(p) for p in e['LEAN_PATH'].split(':') if '/.lake/' not in p and '/backend/' not in p and not p.startswith('/home/dombarker/.elan')];rows=[];broken=[]
for root in roots:
 for src in [*root.rglob('*.olean'), *root.rglob('*.ir'), *root.rglob('*.ilean')]:
  if not src.is_file():broken.append(str(src));continue
  for ext in ['', '.private','.server']:
   source=Path(str(src)+ext)
   if not source.is_file():continue
   p=D/'lean-objects'/source.relative_to(root)
   if p.is_symlink() and not p.exists():p.unlink()
   if not p.exists():
    p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(source)
    rows.append(dict(link=str(p),target=str(source),sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
(D/'cache-overlay-transitive.json').write_text(json.dumps(dict(added=rows,skipped_broken=broken),indent=2)+'\n');print('added',len(rows),'broken skipped',len(broken))

#!/usr/bin/env python3
"""Complete first-directory namespace resolution with read-only cache links.

Never link planned compile outputs and never replace any existing file. The
first cold pass exposed Lean's directory-level resolution of sibling modules.
"""
from pathlib import Path
import hashlib,json
W=Path(__file__).resolve().parent
base=Path('/home/dombarker/project-offloads')
objects=W.parent/'objects'
env=json.loads((W.parent/'build/J.json').read_text())
plan=json.loads((W/'plan.json').read_text())
targets=set(plan['ordered_missing_modules'])
providers={}
for root in map(Path,env['LEAN_PATH'].split(':')):
 for p in root.rglob('*.olean'):
  if p.is_file():providers.setdefault(str(p.relative_to(root))[:-6].replace('/','.'),p)
links=[]
for m,p in sorted(providers.items()):
 dest=objects/(m.replace('.','/')+'.olean')
 if m in targets:
  assert not dest.is_symlink(),m
  continue
 if dest.exists():
  assert dest.is_symlink() and dest.resolve()==p.resolve(),m
 else:
  dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(p)
 for companion,target in [(Path(str(p)+s),Path(str(dest)+s)) for s in ['.private','.server']]+[(p.with_suffix('.ir'),dest.with_suffix('.ir'))]:
  if companion.is_file() and not target.exists():target.symlink_to(companion)
 links.append({'module':m,'provider':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(W/'overlay-links.json').write_text(json.dumps(links,indent=2)+'\n')
print('Read-only cache links:',len(links),'excluded build outputs:',len(targets),flush=True)

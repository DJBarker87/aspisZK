#!/usr/bin/env python3
"""Read existing caches, link exact matches into a new private cache only."""
from pathlib import Path
import hashlib,json
W=Path(__file__).resolve().parent
roots=[Path('/home/dombarker/project-offloads/terminal-v4-begin-mu-canonical-v1-20261019/prebuilt'),Path('/home/dombarker/project-offloads/terminal-v4-begin-challenges-canonical-v1-20261019/prebuilt'),Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022/cache-census'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
rows=json.loads((W/'imports.json').read_text())['modules'];cache=W/'cache';cache.mkdir(exist_ok=True)
seen={};needed=[];reused=[]
def sha(p):
 q=str(p.resolve())
 if q not in seen:seen[q]=hashlib.sha256(p.read_bytes()).hexdigest()
 return seen[q]
for row in rows:
 for f in row['files']:
  rel=Path(f['relative']);assert '..' not in rel.parts and not rel.is_absolute()
  out=cache/rel;out.parent.mkdir(parents=True,exist_ok=True)
  if out.exists():assert sha(out)==f['sha256'];continue
  candidates=[r/rel for r in roots]
  match=next((p for p in candidates if p.is_file() and sha(p)==f['sha256']),None)
  if match:
   out.symlink_to(match.resolve());reused.append(dict(relative=str(rel),path=str(match.resolve()),sha256=f['sha256']))
  else:needed.append(f)
(W/'needed.json').write_text(json.dumps(needed,separators=(',',':'))+'\n')
(W/'reused.json').write_text(json.dumps(reused,separators=(',',':'))+'\n')
print(json.dumps(dict(needed=len(needed),bytes=sum(f['bytes'] for f in needed),reused=len(reused))))

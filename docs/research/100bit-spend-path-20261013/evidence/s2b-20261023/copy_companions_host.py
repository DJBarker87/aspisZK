#!/usr/bin/env python3
import pathlib,json,hashlib,shutil
base=pathlib.Path(__file__).resolve().parent
backend=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend')
roots=[backend/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in (backend/'.lake/packages').iterdir()]]
rows=json.loads((base/'companion-manifest.json').read_text());missing=[];copied=0
for rel,item in rows.items():
 target=base/'objects'/rel
 if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest()==item['sha256']:continue
 src=next((root/rel for root in roots if (root/rel).exists() and hashlib.sha256((root/rel).read_bytes()).hexdigest()==item['sha256']),None)
 if src is None:missing.append(rel);continue
 target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target);copied+=1
(base/'missing-companions.json').write_text(json.dumps(missing)+'\n')
print({'copied':copied,'missing':len(missing)})

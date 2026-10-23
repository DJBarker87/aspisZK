#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess
base=pathlib.Path(__file__).resolve().parent
manifest=json.loads((base/'cache-manifest.json').read_text())
rows={}
for module,item in manifest['modules'].items():
 if '/.elan/toolchains/' in item['path']:continue
 path=pathlib.Path(item['path']);rel=pathlib.Path(*module.split('.'))
 for suffix in ['.olean.server','.olean.private','.ir']:
  p=path.with_suffix(suffix)
  if p.exists():rows[str(rel.with_suffix(suffix))]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
(base/'companion-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
remote='/home/dombarker/project-offloads/codex-cx-s2b-20261023'
subprocess.run(['rsync','-a',str(base/'companion-manifest.json'),str(base/'copy_companions_host.py'),'dombarker@100.108.41.90:'+remote+'/'],check=True)
subprocess.run(['ssh','dombarker@100.108.41.90','python3',remote+'/copy_companions_host.py'],check=True)
missing=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',remote+'/missing-companions.json'],text=True))
groups={}
for rel in missing:
 path=rows[rel]['path'];root=path[:-len(rel)];groups.setdefault(root,[]).append(rel)
for root,rels in groups.items():
 subprocess.run(['rsync','-aL','--files-from=-',root,'dombarker@100.108.41.90:'+remote+'/objects/'],input='\n'.join(rels)+'\n',text=True,check=True)
print({'companions':len(rows),'transferred_missing':len(missing)})

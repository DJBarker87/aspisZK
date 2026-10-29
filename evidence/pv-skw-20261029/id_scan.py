from pathlib import Path
import os,re,json
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029');hits=[]
for root,dirs,files in os.walk(D.parent):
 p=Path(root)
 if p==D:dirs[:]=[];continue
 if len(p.relative_to(D.parent).parts)>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','client-target','objects','lean-objects','actual-objects','sources','lean-sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo','frozen','external'}]
 for name in dirs+files:
  if re.search(r'(?<![A-Za-z0-9])687\d\d(?![A-Za-z0-9])',name):hits.append(str(p/name))
 for name in files:
  if name=='sent.txt':
   for line in (p/name).read_text().splitlines():
    if re.search(r'\b687\d\d\b',line):hits.append(str(p/name)+':'+line)
(D/'id-preflight.json').write_text(json.dumps(dict(range=[68700,68799],collisions=hits),indent=2)+'\n');assert not hits,hits
print('ID block clear')

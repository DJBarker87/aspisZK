from pathlib import Path
import os,re,json
root=Path('/home/dombarker/project-offloads');hits=[]
for here,dirs,files in os.walk(root):
 depth=len(Path(here).relative_to(root).parts)
 dirs[:]=[d for d in dirs if depth<6 and d not in ['target','native-target','charon-target','node_modules','.git','.lake','src','sources','lean-objects','objects','objects2','retained-objects']]
 for n in dirs+files:
  if re.search(r'(?<![0-9])385[0-9]{2}(?![0-9])',n):hits.append(str(Path(here)/n))
 for n in files:
  if n=='sent.txt':
   for line in (Path(here)/n).read_text().splitlines():
    if re.search(r'(?<![0-9])385[0-9]{2}(?![0-9])',line):hits.append(dict(path=str(Path(here)/n),line=line))
print(json.dumps(dict(range=[38500,38599],hits=hits),indent=2))

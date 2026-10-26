"""Read-only locate retained source/object associations for unresolved modules."""
import os,json,sys,hashlib
from pathlib import Path
x=json.load(sys.stdin);g=x['plan'];old=x['historical'];wanted={m:m.replace('.','/')+'.lean' for m in g['unresolved']};names={Path(p).name for p in wanted.values()};matches={};root=Path('/home/dombarker/project-offloads');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();skip={'target','.git','node_modules','RPz_sources','RPz2_sources','RPz_objects','RPz_trusted','objects','objects-S','merged-objects','lib','incremental','deps'}
for base,dirs,files in os.walk(root):
 dirs[:]=[d for d in dirs if d not in skip and not d.endswith('.scope')]
 for f in names.intersection(files):
  p=Path(base)/f
  for m,suffix in wanted.items():
   if not str(p).endswith('/'+suffix):continue
   candidates=[p.with_suffix('.olean')]
   for ancestor in list(p.parents)[:5]:
    for nm in ['objects','objects-S','merged-objects','.lake/build/lib/lean']:
     candidates.append(ancestor/nm/(m.replace('.','/')+'.olean'))
   expected=old.get(m,{}).get('object_sha256');pair=next((q for q in candidates if q.is_file() and expected and sha(q)==expected),None)
   row={'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size,'associated_object':str(pair) if pair else None,'associated_object_sha256':expected if pair else None}
   matches.setdefault(m,[]).append(row)
print(json.dumps(matches,indent=2))

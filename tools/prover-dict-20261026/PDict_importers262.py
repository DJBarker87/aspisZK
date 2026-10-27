"""Read backend imports to distinguish module reachability from axiom use."""
from pathlib import Path
import hashlib,json,re
from functools import lru_cache
job=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/formatter262')
j=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources')
b=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend')
x=json.loads((job/'closure-input.json').read_text());seen={}
def visit(m):
 if m in seen:return
 p=next((r/(m.replace('.','/')+'.lean') for r in [j,b] if (r/(m.replace('.','/')+'.lean')).exists()),None)
 if p is None:return
 s=p.read_text();children=re.findall(r'^import\s+(\S+)',s,re.M)
 seen[m]=dict(source_path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=children)
 for c in children:visit(c)
for m in x['roots']:visit(m)
@lru_cache(None)
def path(m):
 if m=='Aeneas.Std.Core.Fmt':return [m]
 for c in seen.get(m,{}).get('imports',[]):
  rest=path(c)
  if rest:return [m]+rest
 return None
paths={m:path(m) for m in x['modules']}
(job/'formatter-importers.json').write_text(json.dumps(dict(axiom='Aeneas.Std.core.fmt.Formatter',defining_module='Aeneas.Std.Core.Fmt',backend_source=seen['Aeneas.Std.Core.Fmt'],backend_module_inventory={m:v for m,v in seen.items() if m.startswith('Aeneas')},import_paths={m:p for m,p in paths.items() if p},qualification='Import paths alone do not establish an axiom dependency of any declaration.'),indent=2)+'\n')
(job/'Fmt.lean.txt').write_text((b/'Aeneas/Std/Core/Fmt.lean').read_text())
print(len(seen),sum(p is not None for p in paths.values()))

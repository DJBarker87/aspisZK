"""Import-only retargeting of lower native arithmetic proof dependencies."""
from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;L=Path('lean')
closure={}
for line in (E.parent/'replay-deployed2-20261027/RPx_0038/stdout.log').read_text().splitlines():
 if line.startswith('RPX_IMPORTS '):
  row=json.loads(line[len('RPX_IMPORTS '):]);closure[row['module']]=row['imports']
prefixes=['RPx_','RPv_','RPu_','RPt_','RPz8_','RPz7_','RPz4_','RPz_']
selected={}
for m in closure:
 for p in prefixes:
  if m.startswith(p):
   old=m[len(p):]
   if old not in closure:selected[old]=m
   break
# Existing explicit names handle flattened dotted names and generic-only tails.
selected.update(json.loads((E/'NCD_RETARGET_MAP.json').read_text()))
imports=lambda s:re.findall(r'^import\s+(\S+)',s,re.M)
seen={};new=[]
def visit(m):
 if m in selected:return selected[m]
 if m in seen:return seen[m]
 p=L/(m.replace('.','/')+'.lean')
 if not p.exists():seen[m]=m;return m
 text=p.read_text();deps=imports(text);mapped=[visit(d) for d in deps]
 if mapped==deps:seen[m]=m;return m
 name='NCD_B_'+m.replace('.','_');seen[m]=name
 for a,b in zip(deps,mapped):text=re.sub(r'^import '+re.escape(a)+r'$',lambda _: 'import '+b,text,flags=re.M)
 dest=L/(name+'.lean');dest.write_text('-- Inherited body, import-only deployed-cohort retarget.\n'+text)
 new.append(dict(original=m,module=name,path=str(dest),imports=mapped))
 return name
roots=['NBQ_RawCell','NBQ_Powers29','NBQ_TailDomain','NBQ_U06']+imports(Path('lean/NCD_Audit.lean').read_text())+['NBS_GeometryDomains']
for p in L.glob('NCD_*.lean'):
 if not p.stem.startswith(('NCD_B_','NCD_R_')):
  roots += [m for m in imports(p.read_text()) if not m.startswith('NCD_')]
for m in roots:visit(m)
(E/'NCD_LOWER_RETARGET_PLAN.json').write_text(json.dumps(new,indent=2)+'\n')
for row in json.loads((E/'NCD_RETARGET_PLAN.json').read_text()):
 p=Path(row['path']);s=p.read_text()
 for a,b in seen.items():
  if a!=b:s=re.sub(r'^import '+re.escape(a)+r'$',lambda _: 'import '+b,s,flags=re.M)
 p.write_text(s)
(E/'NCD_LOWER_RETARGET_MAP.json').write_text(json.dumps({a:b for a,b in seen.items() if a!=b},indent=2)+'\n')
for p in L.glob('NCD_*.lean'):
 if not p.stem.startswith(('NCD_B_','NCD_R_')):
  s=p.read_text()
  for a,b in seen.items():
   if a!=b:s=re.sub(r'^import '+re.escape(a)+r'$',lambda _: 'import '+b,s,flags=re.M)
  p.write_text(s)
print(len(new), 'lower import-only modules')
print('\n'.join(r['module'] for r in new))

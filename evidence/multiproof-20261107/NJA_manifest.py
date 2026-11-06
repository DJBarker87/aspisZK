"""Select only accepted modules reachable from the final NJA import."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).parent;D=E/'NJA_lean'
base={x['module']:x for x in map(json.loads,(E.parent/'ledger13-20261107/NIU_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
selected={};roots=['AspisR1.RPx_Deployed.deployed']
def walk(m):
 if m in selected:return
 f=D/(m.replace('.','/')+'.lean')
 if not f.exists():
  if m=='NDD_WellformedModel':f=E/'NJA_deps/NDD_WellformedModel.lean'
  else:assert m in base,m;return
 s=f.read_text();imports=re.findall(r'^import (?:all )?([\w.]+)',s,re.M)
 selected[m]={'module':m,'imports':list(dict.fromkeys(['Init']+imports))}
 ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 for n in re.findall(r'^#print axioms ([\w.]+)',s,re.M):
  if n.startswith('NJA_') or n.startswith('AspisR1.'):full=n
  elif ns:full=ns[1]+'.'+n
  else:full=n
  if full not in roots:roots.append(full)
 for i in imports:walk(i)
walk('NJA_COMBINED_IMPORT')
base.update(selected)
(E/'NJA_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(base[k])+'\n' for k in sorted(base)))
(E/'NJA_AUDIT_ROOTS.json').write_text(json.dumps({'roots':roots,'groups':[roots]},indent=2)+'\n')
(E/'NJA_AUDIT_MODULES.json').write_text(json.dumps([['NJA_COMBINED_IMPORT']])+'\n')
(E/'NJA_SELECTED_MODULES.json').write_text(json.dumps({m:{'source':str((D/(m.replace('.','/')+'.lean')).relative_to(E)) if m!='NDD_WellformedModel' else 'NJA_deps/NDD_WellformedModel.lean','imports':v['imports']} for m,v in selected.items()},indent=2)+'\n')
print('NJA manifest:',len(selected),'modules,',len(roots),'roots; baseline imports retained')

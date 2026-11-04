from pathlib import Path
import json
E=Path(__file__).resolve().parent
mods=['NGO_CanonicalPort','NGO_SourceDomain','NGO_CallCases','NGO_PrefixWidePort','NGO_ValidatorErrors','NGO_PrefixHighPort','NGO_ValidatorWord','NGO_PrefixLimbsLaw','NGO_ValidatorCallback','NGO_ValidatorWindows']
visited=set();sources=[]
def visit(m):
 if m in visited:return
 p=E/(m.replace('.','/')+'.lean')
 if not p.exists():return
 visited.add(m);sources.append((m,p))
 for l in p.read_text().splitlines():
  if l.startswith('import '):
   for i in l[7:].split():visit(i)
for m in mods:visit(m)
roots=['AspisR1.RPx_Deployed.deployed']
for m,p in sources:
 ns=''
 for l in p.read_text().splitlines():
  if l.startswith('namespace '):ns=l.split()[1]
  if l.startswith('#print axioms '):
   n=l.split()[2];roots.append(n if n.startswith('NGO_') else ns+'.'+n)
assert len(roots)==len(set(roots))
(E/'NGO_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i:i+10]for i in range(0,len(roots),10)],modules=[m for m,p in sources]),indent=2))
(E/'NGO_COMBINED_IMPORT.lean').write_text('import NGJ_VERIFIER_IMPORT\n'+'\n'.join('import '+m for m in mods)+'\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
tables={}
for name in ['ledger8-20261105/NGJ_EXPECTED_IMPORTS.jsonl','slice-d-parser-20261104/NGD_EXPECTED_IMPORTS.jsonl']:
 for l in (E.parent/name).read_text().splitlines():
  d=json.loads(l);tables.setdefault(d['module'],d['imports'])
for m,p in sources+[("NGO_COMBINED_IMPORT",E/'NGO_COMBINED_IMPORT.lean')]:
 tables[m]=list(dict.fromkeys(['Init']+[i for l in p.read_text().splitlines()if l.startswith('import ')for i in l[7:].split() if i!='all']))
(E/'NGO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n' for m,im in sorted(tables.items())))
print('New roots + headline:',len(roots),'selected source modules:',len(sources),'baseline modules:',len(tables))

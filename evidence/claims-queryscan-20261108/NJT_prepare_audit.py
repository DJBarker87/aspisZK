from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;accepted={}
for pattern in ['NJT_L[0-9][0-9][0-9]/receipt.json','NJT_QL[0-9][0-9][0-9]/receipt.json']:
 for p in sorted(E.glob(pattern)):
  r=json.loads(p.read_text())
  if r['kind']=='lean' and r['exit_status']==0:accepted[r['module']]=r
sources={p.stem:p for p in E.glob('NJT_*.lean') if not p.stem.startswith('NJT_Inspect') and p.stem not in ['NJT_Driver','NJT_ProofDriver','NJT_COMBINED_IMPORT','NJT_Statements']}
for p in (E/'NJT_Q_generated').glob('*.lean'):
 if 'Inspect' not in p.stem:sources[p.stem]=p
mods=[];roots=['AspisR1.RPx_Deployed.deployed'];excluded=[]
for name,p in sorted(sources.items()):
 r=accepted.get(name);h=hashlib.sha256(p.read_bytes()).hexdigest()
 if not r or h not in r['source_hashes'].values():excluded.append(dict(module=name,sha256=h,reason='No successful current-source compile'));continue
 mods.append(dict(module=name,attempt=r['attempt'],source=str(p.relative_to(E)),sha256=h))
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  m=re.match("'([^']+)'",line)
  if m and m[1] not in roots:roots.append(m[1])
assert not excluded,excluded
assert {'NJT_ClaimsRoot','NJT_ClaimsWindows','NJT_QReached','NJT_QLeaves','NJT_QClaimsCanonical'}.issubset({x['module'] for x in mods})
(E/'NJT_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
(E/'NJT_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+24] for i in range(0,len(roots),24)]),indent=2)+'\n')
(E/'NJT_COMBINED_IMPORT.lean').write_text('\n'.join('import '+n for n in ['NJO_COMBINED_IMPORT','NJM_COMBINED_IMPORT',*[m['module'] for m in mods]])+'\n'+'\n'.join('#print axioms '+n for n in roots)+'\n')
rows={};variants=[]
for path in [E.parent/'ledger15-20261108/NJO_EXPECTED_IMPORTS.jsonl',E.parent/'verify-observed7-20261108/NJM_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  x=json.loads(line);n=x['module']
  if n in rows and rows[n]['imports']!=x['imports']:variants.append(dict(module=n,old=rows[n],new=x))
  rows[n]=x
for n,p in [('NJT_COMBINED_IMPORT',E/'NJT_COMBINED_IMPORT.lean'),*[(m['module'],sources[m['module']]) for m in mods]]:
 imports=re.findall(r'^import ([\w.]+)',p.read_text(),re.M)
 rows[n]=dict(module=n,imports=list(dict.fromkeys(['Init',*imports])))
(E/'NJT_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n' for n in sorted(rows)))
(E/'NJT_IMPORT_VARIANTS.json').write_text(json.dumps(variants,indent=2)+'\n')
(E/'NJT_AUDIT_MODULES.json').write_text(json.dumps([m['module'] for m in mods],indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=(len(roots)+23)//24,expected_import_variants=len(variants))))

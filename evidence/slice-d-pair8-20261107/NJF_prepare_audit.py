"""Focused changed-closure audit catalog; unchanged raw walker and fixture laws."""
from pathlib import Path
import json,hashlib,re,difflib
E=Path(__file__).resolve().parent
excluded={'NJF_Driver','NJF_ProofDriver','NJF_COMBINED_IMPORT'}
semantic=[p for p in sorted(E.glob('NJF_*.lean')) if p.stem not in excluded]
(E/'NJF_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NIU_COMBINED_IMPORT\nimport NIW_COMBINED_IMPORT\n'+''.join('import '+p.stem+'\n' for p in semantic)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
# Reaudit new roots and predecessor's source capsule in the changed combined environment.
roots=[r for g in json.loads((E.parent/'slice-d-pair7-20261107/NIW_AUDIT_ROOTS.json').read_text())['groups'] for r in g]
for p in semantic:
 ns=re.findall(r'^namespace (\S+)',p.read_text(),re.M)
 assert len(ns)==1,p
 for n in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):
  root=n if n.startswith('AspisR1.') else ns[0]+'.'+n
  if root not in roots:roots.append(root)
assert roots.count('AspisR1.RPx_Deployed.deployed')==1
(E/'NJF_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
rows={};provenance=[]
for name in ['slice-d-pair7-20261107/NIW_EXPECTED_IMPORTS.jsonl','ledger13-20261107/NIU_EXPECTED_IMPORTS.jsonl']:
 p=E.parent/name
 for line in p.read_text().splitlines():
  row=json.loads(line)
  assert row['module'] not in rows or rows[row['module']]['imports']==row['imports'],('catalog conflict',row['module'])
  rows[row['module']]=row
 provenance.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for p in semantic+[E/'NJF_COMBINED_IMPORT.lean']:
 imports=['Init']+[n for line in p.read_text().splitlines() if line.startswith('import ') for n in line[7:].split()]
 rows[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(imports)))
(E/'NJF_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n'for n in sorted(rows)))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(E/'NJF_AUDIT_PROVENANCE.json').write_text(json.dumps(dict(base_catalogs=provenance,semantic_modules=[dict(path=p.name,sha256=sha(p))for p in semantic],roots=len(roots),walker_c_sha256=sha(E/'NJF_NFA_WALKER.c.txt'),walker_unchanged=sha(E/'NJF_NFA_WALKER.c.txt')==sha(E.parent/'slice-d-pair7-20261107/NIW_NFA_WALKER.c.txt'),prior_NIU_full_raw_audit='NIU 8182 roots retained; this is the focused changed-root closure plus all NIW source roots and headline, scanned in the full NIU+NGK+NIW import'),indent=2)+'\n')
print(json.dumps(dict(roots=len(roots),modules=len(semantic),catalog_modules=len(rows))))

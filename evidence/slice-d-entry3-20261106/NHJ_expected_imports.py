from pathlib import Path
import json,hashlib,sys
E=Path(__file__).resolve().parent;rows={};provenance=[]
for f in [E.parent/'pool-retarget-20261105/NGK_EXPECTED_IMPORTS.jsonl',E.parent/'slice-d-entry2-20261106/NHD_EXPECTED_IMPORTS.jsonl']:
 provenance.append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
 for l in f.read_text().splitlines():
  x=json.loads(l)
  if x['module'] in rows:assert rows[x['module']]['imports']==x['imports'],x['module']
  rows[x['module']]=dict(module=x['module'],imports=x['imports'])
for p in E.glob('NHJ_*.lean'):
 if p.stem in ['NHJ_ProofDriver','NHJ_ScanDriver']:continue
 imports=['Init']
 for l in p.read_text().splitlines():
  if l.startswith('import '):
   for n in l[7:].split():
    if n!='all' and n not in imports:imports.append(n)
 rows[p.stem]=dict(module=p.stem,imports=imports)
 provenance.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=imports))
raw=''.join(json.dumps(rows[n])+'\n' for n in sorted(rows));p=E/'NHJ_EXPECTED_IMPORTS.jsonl'
if '--write' in sys.argv:p.write_text(raw);(E/'NHJ_EXPECTED_IMPORT_PROVENANCE.json').write_text(json.dumps(provenance,indent=1)+'\n')
else:assert p.read_text()==raw
print(json.dumps(dict(status='PASS',expected_modules=len(rows))))

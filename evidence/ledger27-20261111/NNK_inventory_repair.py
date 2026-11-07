"""Repair only missing/stale expected imports from independent committed source."""
from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;loaded=[json.loads(l)for l in(E/'NNK_LOADED_scan.jsonl').read_text().splitlines()];bad=[r for r in loaded if r['dangling']or r['duplicate_owners']or not r['imports_match']];assert all(not r['dangling']and not r['duplicate_owners']for r in bad)
(E/'NNK_FAILED_SCAN59.json').write_text(json.dumps(dict(status='FAILED_EXPECTED_IMPORT_INVENTORY_ONLY',rows=bad,dangling=0,canonical_duplicate_owners=0),indent=1)+'\n')
p=E/'NNK_EXPECTED_IMPORTS.jsonl';(E/'NNK_EXPECTED_IMPORTS_BEFORE_REPAIR.jsonl').write_bytes(p.read_bytes());expected={json.loads(l)['module']:json.loads(l)['imports']for l in p.read_text().splitlines()};review=[]
for r in bad:
 m=r['module']
 folder='tx1-observed3-20261110'if m.startswith('NMP_')else'model-bridge-20261111'if m.startswith('NND_')else'tx1-principal-20261111'if m.startswith('NNG_')else'tx2-auth-20261111'
 source='evidence/'+folder+'/'+m+'.lean';b=subprocess.check_output(['git','show','HEAD:'+source]);imports=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',b.decode(),re.M)))
 assert imports==r['imports'],(m,source,imports,r['imports'])
 review.append(dict(module=m,source=source,source_sha256=hashlib.sha256(b).hexdigest(),before=expected.get(m),source_derived_imports=imports,actual_matches_independent_source=True));expected[m]=imports
p.write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
(E/'NNK_IMPORT_INVENTORY_REPAIR.json').write_text(json.dumps(dict(status='PASS_SOURCE_PREFLIGHT',entries=review,count=len(review),reason='18 previously unloaded NMP modules and5 NND modules omitted;2 stale WIP import entries inherited from NNI inventory. No source/scanner logic or theorem changed; every corrected import list independently equals committed source.'),indent=1)+'\n');print('source-derived repaired entries',len(review))

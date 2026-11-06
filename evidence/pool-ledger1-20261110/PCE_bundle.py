"""Package exact committed/source evidence for the last capped validation scope."""
from pathlib import Path
import json,lzma,base64,hashlib
from PCE_build_ledger import E,R,inputs
names=['PCE_VALIDATOR.py','PCE_build_ledger.py','PCE_AUDIT.json','PCE_SCAN.json','PCE_STATEMENTS.json','PCE_ROOTS.json','PCE_GROUPS.json','PCE_COMPOSITION.json','PCE_LEDGER.json' if (E/'PCE_LEDGER.json').exists() else 'PCE_LEDGER.json.xz']+['PCE_binary_roots'+str(i)+'.json' for i in range(13)]
paths=[E/n for n in names]+[R/n for n in inputs()]
for i in [1,4,5,6,8]+list(range(9,25)):paths += [E/f'PCE_L{i:03d}'/'receipt.json',E/f'PCE_L{i:03d}-admission.json']
files={str(p.relative_to(R)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),data=base64.b64encode(lzma.compress(p.read_bytes(),preset=6)).decode()) for p in paths}
(E/'PCE_VALIDATION_BUNDLE.json').write_text(json.dumps(files)+'\n')
print('Prepared '+str(len(files))+' exact hashed validator inputs; no native or proof execution.')

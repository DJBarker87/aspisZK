"""Prepare exact import expectations and raw roots; never infer credit here."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
expected={x['module']:x['imports'] for x in map(json.loads,(E.parent/'ledger23-20261110/NLS_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for x in map(json.loads,(E.parent/'pc-helpers1-20261110/PCB_EXPECTED_IMPORTS.jsonl').read_text().splitlines()):expected.setdefault(x['module'],x['imports'])
for folder,prefixes in [(E.parent/'sdk-borrow-20261109',('NLF_',)),(E.parent/'pc-deposit-pilot-20261110',('PCA_',)),(E.parent/'pc-deposit2-20261110',('PCC_',)),(E,('PCF_',))]:
 for p in folder.glob('*.lean'):
  if not p.name.startswith(prefixes):continue
  names=['Init']+sum((s[7:].split() for s in p.read_text().splitlines() if s.startswith('import ')),[])
  expected[p.name[:-5]]=list(dict.fromkeys(names))
(E/'PCF_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps({'module':m,'imports':v})+'\n' for m,v in sorted(expected.items())))

modules=['PCF_Count','PCF_AccountLaws','PCF_Payer','PCF_Token','PCF_LaneShape','PCF_LaneValue','PCF_ChildLaws','PCF_WordBridge','PCF_CountWord','PCF_SliceFrame','PCF_CopyRange','PCF_EncodePrefix','PCF_DigestFirst','PCF_FirstStub','PCF_CanonicalWords','PCF_LaneModel']
import re
own=[m+'.'+n for m in modules for n in re.findall(r'^#print axioms (\w+)$',(E/(m+'.lean')).read_text(),re.M)]
base=json.loads((E/'PCF_ALL_AUDIT_ROOTS.json').read_text())['roots']
roots=list(dict.fromkeys(base+own))
(E/'PCF_STAGE2_ROOTS.json').write_text(json.dumps(dict(roots=roots,own=own),indent=1)+'\n')
t=json.loads((E/'PCF_TASKS.json').read_text())
t['PCF_L064']=dict(kind='lean',target='PCF_COMBINED_IMPORT')
t['PCF_L065']=dict(kind='audit',target='Stage2 combined import scan',command=['PCF_native/PCF_AuditDriver','scan'],files={'PCF_EXPECTED_IMPORTS.jsonl':'PCF_EXPECTED_IMPORTS.jsonl','PCF_AUDIT_ROOTS.json':'PCF_STAGE2_ROOTS.json'},collect=['PCF_LOADED_scan.jsonl'])
raw=[]
for i in range(0,len(roots),20):
 name=f'PCF_STAGE2_ROOTS_{i//20:02}.json';(E/name).write_text(json.dumps(dict(roots=roots[i:i+20]),indent=1)+'\n')
 a=f'PCF_L{66+i//20:03}';raw.append(a);t[a]=dict(kind='audit',target='Stage2 raw ax2 root batch '+str(i//20),command=['PCF_native/PCF_AuditDriver',f'proof{20+i//20}'],files={'PCF_AUDIT_ROOTS.json':name})
(E/'PCF_STAGE2_PLAN.json').write_text(json.dumps(dict(combined='PCF_L064',scan='PCF_L065',raw_batches=raw,fixtures='PCF_L023',binary='PCF_AUDIT_BINARY_PINS.json',same_binary=True),indent=1)+'\n')
(E/'PCF_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
print('PCF stage2 prepared',len(roots),'roots',len(own),'own')

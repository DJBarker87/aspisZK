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


import re
modules=['PCF_Iterator','PCF_ArrayIndex','PCF_EncodeByte','PCF_AppendEncoder','PCF_DigestShape','PCF_ResultAssoc','PCF_CopyMap','PCF_AppendStep','PCF_AppendStop','PCF_AppendLoop','PCF_AppendComplete','PCF_CountSlice','PCF_CountSliceState']
new=[m+'.'+n for m in modules for n in re.findall(r'^#print axioms (\w+)$',(E/(m+'.lean')).read_text(),re.M)]
old=json.loads((E/'PCF_STAGE2_ROOTS.json').read_text());roots=list(dict.fromkeys(old['roots']+new));own=list(dict.fromkeys(old['own']+new))
(E/'PCF_FINAL_ROOTS.json').write_text(json.dumps(dict(roots=roots,own=own,new=new),indent=1)+'\n')
(E/'PCF_FINAL_NEW_ROOTS.json').write_text(json.dumps(dict(roots=['AspisR1.RPx_Deployed.deployed']+new),indent=1)+'\n')
t=json.loads((E/'PCF_TASKS.json').read_text());t['PCF_L111']=dict(kind='lean',target='PCF_COMBINED_IMPORT')
t['PCF_L112']=dict(kind='audit',target='Final NFX scan with complete append reference',command=['PCF_native/PCF_AuditDriver','scan'],files={'PCF_EXPECTED_IMPORTS.jsonl':'PCF_EXPECTED_IMPORTS.jsonl','PCF_AUDIT_ROOTS.json':'PCF_FINAL_ROOTS.json'},collect=['PCF_LOADED_scan.jsonl'])
t['PCF_L113']=dict(kind='audit',target='Final new roots and headline raw ax2',command=['PCF_native/PCF_AuditDriver','proof40'],files={'PCF_AUDIT_ROOTS.json':'PCF_FINAL_NEW_ROOTS.json'})
t['PCF_L114']=dict(t['PCF_L077']);t['PCF_L114']['target']='Final streamed raw graphs and immutable import/binary verification'
(E/'PCF_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
print('PCF final prepared',len(roots),'total roots',len(own),'own',len(new),'new')

"""Only ax2-authorized module/path/manifest adaptations of retained NKW drivers."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
for name in ['Driver','ProofDriver','batch']:
 suffix='.py'if name=='batch'else'.lean'
 p=E.parent/'ledger20-20261109'/('NKW_'+name+suffix)
 (E/('NLD_'+name+suffix)).write_text(p.read_text().replace('NKW_','NLD_'))
expected={};conflicts=[]
for folder,pre in [('ledger20-20261109','NKW'),('entry-sdk-20261108','NJN')]:
 for line in (E.parent/folder/(pre+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  row=json.loads(line);m=row['module'];v=row['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v))
  else:expected[m]=v
for p in E.glob('NLD_*.lean'):
 expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NLD_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
(E/'NLD_EXPECTED_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n');assert not conflicts
roots=['AspisR1.RPx_Deployed.deployed']
for p in E.glob('NLD_*.lean'):
 if p.stem.endswith(('Inspect','COMBINED_IMPORT','Driver')):continue
 text=p.read_text();n=re.search(r'^namespace ([\w.]+)',text,re.M)
 if n:roots+=[n[1]+'.'+m for m in re.findall(r'^#print axioms (\w+)\s*$',text,re.M)]
roots=sorted(set(roots))
(E/'NLD_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=1)+'\n')
(E/'NLD_AUDIT_MODULES.json').write_text(json.dumps([['NLD_COMBINED_IMPORT']])+'\n')
print('audit manifests',len(roots),'roots',len(expected),'expected imports')

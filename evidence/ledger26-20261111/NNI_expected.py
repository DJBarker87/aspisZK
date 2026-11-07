"""Extend import inventory from accepted, source-hash-checked snapshots."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;p=E/'NNI_EXPECTED_IMPORTS.jsonl';expected={r['module']:r['imports']for r in map(json.loads,p.read_text().splitlines())};added=[]
for d,pre,generated in [('tx1-principal-20261111','NNG','NNG_generated'),('tx2-auth-20261111','NMX','NMX_generated'),('lib-20261111','LIB','LIB_generated'),('libb-20261111','LIBB','LIBB_generated'),('libc-20261111','LIBC','LIBC_generated')]:
 for rc in sorted((E.parent/d).glob(pre+'_L*/receipt.json')):
  x=json.loads(rc.read_text())
  if x['exit_status']!=0:continue
  for name,h in x['source_hashes'].items():
   if not name.startswith(generated+'/') or not name.endswith('.lean'):continue
   m=name[len(generated)+1:-5].replace('/','.')
   if m in expected:continue
   src=rc.parent/'sources'/name
   if not src.exists():continue
   b=src.read_bytes();assert hashlib.sha256(b).hexdigest()==h
   expected[m]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',b.decode(),re.M)));added.append(dict(module=m,source=str(src),sha256=h,imports=expected[m]))
p.write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())));(E/'NNI_IMPORT_INVENTORY_ADDITIONS.json').write_text(json.dumps(added,indent=1)+'\n');print('accepted snapshot additions',len(added))

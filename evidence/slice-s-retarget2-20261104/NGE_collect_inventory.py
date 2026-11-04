"""Verify exact named declaration owners from kernel-loaded inventory receipts."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text());spec=J(E/'NGE_CERT_INVENTORY_INPUT.json');mods=None;entries=[]
for i,group in enumerate(spec['groups']):
 a=f'NGE_L{98+i:03}';r=J(E/a/'receipt.json');assert r['exit_status']==0 and r['module']==f'NGE_CertificatePart{i:02}'
 assert (E/a/'sources/NGE_generated'/(r['module']+'.lean')).read_bytes()==(E/(r['module']+'.lean')).read_bytes()
 log=(E/a/'stdout.log').read_text();found=[]
 for line in log.splitlines():
  if 'NGE_CERT_MODULES ' in line:mods=json.loads(line.split('NGE_CERT_MODULES ',1)[1])
  if 'NGE_CERT_ENTRY ' in line:
   row=json.loads(line.split('NGE_CERT_ENTRY ',1)[1]);found.append(row['name']);row.update(parent_attempt=a,source_revision=r['source_revision'],source_sha256=hashlib.sha256((E/(r['module']+'.lean')).read_bytes()).hexdigest());entries.append(row)
 assert set(found)==set(group) and len(found)==len(group),(a,found,group)
assert mods is not None
mismatch=[];absent=[]
for row in entries:
 row['expected_owner']=spec['expected_owners'][row['name']]
 if row['found']:
  nums=re.findall(r'\d+',row['module_idx']);assert len(nums)==1,(row['name'],row['module_idx'])
  row['actual_owner']=mods[int(nums[0])];row['type_sha256']=hashlib.sha256(row['type'].encode()).hexdigest()
  if row['actual_owner']!=row['expected_owner']:mismatch.append(row)
 else:absent.append(row)
assert len(entries)==len({r['name'] for r in entries})==len(spec['expected_owners'])
assert not mismatch,[(r['name'],r['expected_owner'],r['actual_owner']) for r in mismatch]
assert all(r['expected_owner'].startswith(('NEX_','NEY_','NED_')) for r in absent),[r['name'] for r in absent]
out=dict(status='PASS',entries=entries,selected_names=len(entries),found=sum(r['found'] for r in entries),absent=len(absent),incompatible_owners=mismatch,absent_chain_B_only=True,module_index_names=mods,method='Each selected name inspected directly in the same compiled combined forest; actual ConstantInfo type and owner, no module-name inference')
(E/'NGE_DECLARATION_INVENTORY.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(names=len(entries),found=out['found'],absent=out['absent'],mismatches=len(mismatch))))

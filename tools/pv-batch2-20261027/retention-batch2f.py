"""Host-only public key inventory and read-only private cache pins."""
from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
def b58(data):
 a='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=int.from_bytes(data,'big');s=''
 while n:n,i=divmod(n,58);s=a[i]+s
 return '1'*(len(data)-len(data.lstrip(b'\0')))+s
keys=[]
for p in sorted((H/'candidate').glob('*/artifacts/*keypair.json')):
 k=json.loads(p.read_text());assert len(k)==64;p.chmod(0o600)
 keys.append(dict(path=str(p),public_key=b58(bytes(k[32:])),mode=oct(p.stat().st_mode&0o777),retained=True))
(H/'batch2f-key-retention.json').write_text(json.dumps(dict(keys=keys,no_transactions=True,no_key_cleanup=True,refund_destination=None,refund_signatures=[],policy='All keys retained securely. No private halves copied into evidence; no controlled funds or authorities relinquished.'),indent=2)+'\n')
rows=[]
for p in sorted((H/'lean-objects').rglob('*.olean')):
 if p.is_symlink():continue
 b=p.read_bytes();rows.append(dict(path=str(p.relative_to(H)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
(H/'batch2f-object-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
print('retained',len(keys),'keys; pinned',len(rows),'private objects; no cleanup')

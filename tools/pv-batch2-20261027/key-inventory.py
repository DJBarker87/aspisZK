"""Record only public halves and retention permissions; never delete keys."""
from pathlib import Path
import json,os
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
def b58(data):
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=int.from_bytes(data,'big');s=''
 while n:n,i=divmod(n,58);s=alphabet[i]+s
 return '1'*(len(data)-len(data.lstrip(b'\0')))+s
rows=[]
for p in H.glob('candidate/build-*/artifacts/*keypair.json'):
 key=json.loads(p.read_text());assert len(key)==64;p.chmod(0o600)
 rows.append(dict(path=str(p),public_key=b58(bytes(key[32:])),mode=oct(p.stat().st_mode&0o777),retained=True))
(H/'key-retention.json').write_text(json.dumps(dict(keys=rows,no_transactions=True,no_key_cleanup=True,refund_destination=None,refund_signatures=[],policy='All generated task keys retained securely; no balance or authority relinquished.'),indent=2)+'\n')

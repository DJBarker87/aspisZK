"""After the budget stop, retain every key and pin private objects before cache cleanup."""
from pathlib import Path
import json,hashlib,shutil,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
def b58(b):
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=int.from_bytes(b,'big');s=''
 while n:n,i=divmod(n,58);s=alphabet[i]+s
 return '1'*(len(b)-len(b.lstrip(b'\0')))+s
keys=[]
for p in H.rglob('*keypair.json'):
 if p.is_symlink():raise SystemExit('key symlink requires retention inspection: '+str(p))
 key=json.loads(p.read_text());assert isinstance(key,list) and len(key)==64 and all(type(x)is int and 0<=x<=255 for x in key)
 p.chmod(0o600);keys.append(dict(path=str(p),public_key=b58(bytes(key[32:])),mode='0o600',retained=True))
(H/'batch2c-key-retention.json').write_text(json.dumps(dict(keys=keys,no_transactions=True,no_key_cleanup=True,refund_destination=None,refund_signatures=[],policy='No wallet/account key is deleted, moved or relinquished. All keys retained.'),indent=2)+'\n')
objects=[]
for p in (H/'lean-objects').rglob('*.olean'):
 if p.is_symlink():continue
 objects.append(dict(path=str(p.relative_to(H)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(H/'batch2c-output-object-pins.json').write_text(json.dumps(objects,indent=2)+'\n')
def keyshape(v):
 if isinstance(v,list):return (len(v)==64 and all(type(x)is int and 0<=x<=255 for x in v)) or any(keyshape(x) for x in v)
 if isinstance(v,dict):return any(keyshape(x) for x in v.values())
 return False
rows=[]
for name in ['charon-target','lean-objects']:
 p=H/name;assert p.parent==H and not p.is_symlink();files=list(p.rglob('*')) if p.exists() else [];suspect=[]
 for q in files:
  if q.is_symlink() or not q.is_file():continue
  if q.suffix in ['.key','.pem'] or any(s in q.name.lower() for s in ['keypair','wallet-key','secret-key']):suspect.append(str(q));continue
  if q.suffix=='.json':
   try:
    if keyshape(json.loads(q.read_text())):suspect.append(str(q))
   except (ValueError,UnicodeError):pass
 row=dict(path=str(p),entries=len(files),suspected_key_paths=suspect)
 if suspect:row['action']='retained entire cache: potential key material'
 else:
  if p.exists():shutil.rmtree(p)
  row['action']='removed key-free private compiled scratch; shared symlink targets untouched'
 rows.append(row)
assert all(Path(r['path']).exists() and Path(r['path']).stat().st_mode&0o777==0o600 for r in keys)
j=dict(epoch=time.time(),paths=rows,object_pins='batch2c-output-object-pins.json',keys_retained=len(keys),key_inventory='batch2c-key-retention.json',shared_caches='untouched',source_and_evidence='retained',print_axioms='N/A: cache retirement; no compile')
(H/'batch2c-cache-retirement.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))

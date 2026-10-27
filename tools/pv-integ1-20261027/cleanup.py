"""Remove only this job's cargo caches; retain every generated key securely."""
from pathlib import Path
import json,shutil,hashlib,os
H=Path('/home/dombarker/project-offloads/codex-pv-integ1-20261027')
assert H.is_dir();retained=[];removed=[]
def b58(b):
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=int.from_bytes(b,'big');out=''
 while n:n,r=divmod(n,58);out=alphabet[r]+out
 return '1'*(len(b)-len(b.lstrip(b'\0')))+out
for name in ['sbf-target-verifier','sbf-target-pool','native-target']:
 root=H/name
 if not root.exists():
  removed.append(dict(path=str(root),status='already removed by preceding partial cleanup'));continue
 assert root.is_dir() and not root.is_symlink()
 for p in root.rglob('*keypair*.json'):
  if not p.is_file():continue
  raw=p.read_bytes();key=json.loads(raw)
  if not isinstance(key,list):
   assert '.fingerprint' in p.parts, 'Keep unclassified key-like file: '+str(p)
   continue
  assert len(key)==64
  dst=H/'retained-keys'/p.relative_to(H);dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists()
  shutil.move(str(p),str(dst));os.chmod(dst,0o600)
  retained.append(dict(path=str(dst),public_key=b58(bytes(key[32:])),sha256=hashlib.sha256(raw).hexdigest(),action='Key moved securely out of rebuildable cargo cache; retained, never destroyed or spent'))
 shutil.rmtree(root);removed.append(dict(path=str(root),status='removed by completed cleanup'))
# SBF output key files are retained in place; record public identifiers only.
for root in H.glob('build-*/artifacts'):
 for p in root.glob('*keypair*.json'):
  raw=p.read_bytes();key=json.loads(raw);assert len(key)==64;os.chmod(p,0o600)
  retained.append(dict(path=str(p),public_key=b58(bytes(key[32:])),sha256=hashlib.sha256(raw).hexdigest(),action='Retained in place at mode 0600'))
(H/'cleanup.json').write_text(json.dumps(dict(removed_cargo_targets=removed,retained_keys=retained,key_cleanup_authorized=False,keys_deleted=0,refunds='N/A: no key destruction, deployment, account creation or fund movement performed'),indent=2)+'\n')
print('cargo targets removed',len(removed),'keys retained',len(retained))

"""Delete only D325 cargo caches, retaining every key securely."""
from pathlib import Path
import shutil,os,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027');removed=[];keys=[]
def b58(b):
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=int.from_bytes(b,'big');out=''
 while n:n,r=divmod(n,58);out=alphabet[r]+out
 return '1'*(len(b)-len(b.lstrip(b'\0')))+out
for root in [D/'sbf-target-verifier',D/'sbf-target-pool',D/'native-target',D/'baseline/native-target']:
 assert root.parent in [D,D/'baseline'] and not root.is_symlink()
 if not root.exists():removed.append(dict(path=str(root),existed=False));continue
 for p in root.rglob('*keypair*.json'):
  if not p.is_file():continue
  raw=p.read_bytes();key=json.loads(raw)
  if not isinstance(key,list):
   assert '.fingerprint' in p.parts,p
   continue
  assert len(key)==64,p
  dst=D/'retained-keys'/p.relative_to(D);dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists()
  shutil.move(str(p),str(dst));os.chmod(dst,0o600)
  keys.append(dict(path=str(dst),public_key=b58(bytes(key[32:])),action='retained outside deleted cargo target',sha256=hashlib.sha256(raw).hexdigest()))
 shutil.rmtree(root);removed.append(dict(path=str(root),existed=True,removed=True))
for p in D.glob('build-*/artifacts/*keypair*.json'):
 raw=p.read_bytes();key=json.loads(raw);assert isinstance(key,list) and len(key)==64
 os.chmod(p,0o600);keys.append(dict(path=str(p),public_key=b58(bytes(key[32:])),action='retained in place mode0600',sha256=hashlib.sha256(raw).hexdigest()))
r=dict(source_revision=(D/'source-revision.txt').read_text().strip(),removed_cargo_targets=removed,retained_keys=keys,keys_destroyed=0,shared_sources_written=0,transactions_sent=0,refunds='N/A: all keys retained; no wallet/account key cleanup, deployment or fund movement',remaining_cargo_targets=[str(p) for p in [D/'sbf-target-verifier',D/'sbf-target-pool',D/'native-target',D/'baseline/native-target'] if p.exists()])
(D/'cleanup.json').write_text(json.dumps(r,indent=2)+'\n');assert not r['remaining_cargo_targets'];print('Removed D325 cargo caches; retained',len(keys),'keys')

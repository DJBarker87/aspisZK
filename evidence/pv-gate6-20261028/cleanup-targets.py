from pathlib import Path
import json,shutil,time
D=Path(__file__).resolve().parent
names=['sbf-target-verifier','sbf-target-pool','native-target','combined/baseline/native-target']
rows=[]
compiled_metadata=[]
def possible_key(q):
 n=q.name.lower()
 if not ('keypair' in n or n.endswith(('.pem','.key'))):return False
 # These are rustc library artifacts or Cargo fingerprints, not wallet material.
 if 'solana_keypair' in n and (q.suffix in {'.rlib','.rmeta','.d'} or '/.fingerprint/solana-keypair-' in str(q)):
  compiled_metadata.append(str(q));return False
 return True
prior=D/'cleanup.json'
if prior.exists():
 (D/'cleanup-initial.json').write_bytes(prior.read_bytes())
for name in names:
 p=D/name
 if not p.exists():rows.append(dict(path=str(p),existed=False));continue
 assert not p.is_symlink()
 keys=[str(q) for q in p.rglob('*') if q.is_file() and possible_key(q)]
 if keys:
  rows.append(dict(path=str(p),existed=True,deleted=False,retained_possible_keys=keys));continue
 shutil.rmtree(p);rows.append(dict(path=str(p),existed=True,deleted=True))
(D/'cleanup.json').write_text(json.dumps(dict(utc=time.time(),targets=rows,classified_rustc_metadata=compiled_metadata,keys_deleted=0,keys_moved=0,transactions=0,refunds='N/A: no key cleanup authorized or performed'),indent=2)+'\n')
print(json.dumps(rows))

"""Stop-only retention and cache hygiene. No build, proof, or key cleanup."""
from pathlib import Path
import hashlib,json,os,shutil,stat,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
active=subprocess.run(['systemctl','--user','list-units','--type=scope','--state=active','--plain','--no-legend'],capture_output=True,text=True,check=True).stdout
ours=[s for s in active.splitlines() if 'pv-b3-' in s and ('batch3c-' in s or 'lean-379' in s)]
assert not ours,ours
objects=[]
for p in (H/'lean-objects').rglob('*.olean'):
 objects.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'batch3c-object-inventory.json').write_text(json.dumps(objects,indent=1)+'\n')
binary=H/'target/release/batch3b-carrier-bench'; retained=None
if binary.exists():
 dest=H/'bin/batch3c-split-counterexample';dest.parent.mkdir(exist_ok=True);assert not dest.exists();shutil.copy2(binary,dest)
 retained=dict(path=str(dest),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),bytes=dest.stat().st_size,source_revision='1be0505afc')
keys=[]
for d in H.glob('batch3c-*-elf-*'):
 for p in d.glob('artifacts/*keypair.json'):
  p.chmod(0o600);keys.append(dict(path=str(p),mode=oct(stat.S_IMODE(p.stat().st_mode))))
removed=[];kept=[]
for name in ['target','sbf-target','charon-target','lean-objects']:
 p=H/name
 if not p.exists():continue
 sensitive=[q for q in p.rglob('*') if q.is_file() and ('keypair' in q.name.lower() or ('nonce' in q.name.lower() and q.suffix in ['.json','.jsonl','.db']))]
 if sensitive:
  kept.append(dict(path=str(p),reason='possible retained key/nonce data; cache not deleted',files=list(map(str,sensitive))))
  for q in sensitive:q.chmod(0o600)
 else:shutil.rmtree(p);removed.append(str(p))
rec=dict(stop_reason='native fixture disagreement; candidate schedule returns Err(Shape)',active_own_scopes=ours,source_revision='1be0505afc',retained_counterexample_binary=retained,retained_build_keys=keys,keys_deleted=False,nonce_ledgers_deleted=False,removed_private_caches=removed,kept_caches=kept,shared_paths_deleted=False)
(H/'batch3c-cleanup.json').write_text(json.dumps(rec,indent=1)+'\n');print(json.dumps(rec))

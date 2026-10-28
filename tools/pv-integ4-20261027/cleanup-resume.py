"""Remove only this resume's native Cargo caches; retain every task key in place."""
from pathlib import Path
import json,hashlib,stat,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027');old=json.loads((D/'cleanup.json').read_text());retained=[];removed=[]
for k in old['retained_keys']:
 p=Path(k['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==k['sha256'];assert stat.S_IMODE(p.stat().st_mode)==0o600
 retained.append(dict(k,verified_mode='0600',action='retained unchanged in place'))
roots=[D/'combined/baseline/native-target',D/'combined/candidate/native-target']
# Inspect all targets before deleting either. A key-bearing cache is retained whole.
for root in roots:
 assert root.parent in [D/'combined/baseline',D/'combined/candidate'] and not root.is_symlink()
 for p in root.rglob('*keypair*.json'):
  data=json.loads(p.read_text());assert not (isinstance(data,list) and len(data)==64),f'Key-bearing target retained; no deletion authorized: {p}'
for root in roots:
 exists=root.exists()
 if exists:shutil.rmtree(root)
 removed.append(dict(path=str(root),existed=exists,removed=exists))
remaining=[str(p) for p in roots if p.exists()];assert not remaining
assert not (D/'combined/combined-quiet-001').exists() and not (D/'combined/combined-quiet-001-results').exists()
r=dict(source_revision=(D/'source-revision.txt').read_text().strip(),removed_cargo_targets=removed,remaining_targets=remaining,retained_keys=retained,keys_destroyed=0,keys_unlinked=0,keys_moved=0,deployments=0,transactions=0,refunds='N/A: all task keys retained unchanged; no wallet/account cleanup',quiet_timing_run=False,outputs='Binaries, raw corpus, fixture records and oracle streams retained in this job directory')
(D/'cleanup-resume.json').write_text(json.dumps(r,indent=2)+'\n');print('Removed two native targets; retained all three task keys unchanged at0600')

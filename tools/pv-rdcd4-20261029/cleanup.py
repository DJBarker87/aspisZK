"""Post-release removal of only this task's rebuildable build caches.
No source, receipts, artifact manifests, other job directory or key is removed.
"""
from pathlib import Path
import json,shutil,time
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
assert D.is_dir() and not D.is_symlink()
proof=json.load(open(D/'final-coherence-result.json'));assert proof['external_count']==5673
for module in ['R1Z/PV_RDCD4_FinalAudit','R1Z/PV_RDCD4_FocusedReplay','R1Z/PV_RDCD4_FrozenManifest']:
 assert module in proof['modules'],('final release gate missing',module)
removed=[]
for name in ['classification-target','lean-objects','external-objects']:
 p=D/name;assert p.parent==D
 if p.exists():
  assert p.is_dir() and not p.is_symlink(),str(p)
  shutil.rmtree(p);removed.append(str(p))
(D/'cleanup-result.json').write_text(json.dumps(dict(removed=removed,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),preserved=['all sources, own staged sources and receipts','native artifacts and recorded hashes','all other job directories, shared objects and source workspaces','all wallet/account keys; none generated or touched'],qualification='After successful final audit/replay/coherence. Historical object paths/hashes describe measured pre-cleanup files; no post-cleanup availability is claimed.'),indent=2)+'\n')
print('Removed own rebuildable caches only:',removed)

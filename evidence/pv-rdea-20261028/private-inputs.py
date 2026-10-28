from pathlib import Path
import json,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');O=D/'actual-objects';J=D.parent/'aspis-joint-20261019/objects'
old=json.loads((D/'private-cache-preflight.json').read_text());removed=[]
for row in old['rows']:
 p=Path(row['path']);assert p.is_relative_to(O)
 if p.is_symlink():
  assert str(p.readlink())==row['target'];p.unlink();removed.append(str(p))
 for suffix in ['.private','.server']:
  q=Path(str(p)+suffix)
  if q.is_symlink():q.unlink();removed.append(str(q))
e=json.loads((D.parent/'r1-privacy-build-integration-20261019/env/J.json').read_text());e['LEAN_PATH']=str(J)+':'+e['LEAN_PATH'];(D/'private-env-J.json').write_text(json.dumps(e,indent=2)+'\n')
roots=[O]+list(map(Path,e['LEAN_PATH'].split(':')));authority=json.loads((D.parent/'codex-pv-rdb1-20261028/external-object-manifest.json').read_text());checked=[]
for row in authority:
 rel=row['module'].replace('.','/')+'.olean';p=next((r/rel for r in roots if (r/rel).exists()),None)
 assert p is not None,row['module'];actual=hashlib.sha256(p.read_bytes()).hexdigest();assert actual==row['object_sha256'],(row['module'],actual,row['object_sha256'])
 checked.append(dict(module=row['module'],path=str(p),sha256=actual))
(D/'private-inputs.json').write_text(json.dumps(dict(ok=True,removed_own_cache_links=removed,shared_paths_modified=[],checked=checked,env=e,reason='run2 always prefixes its objects argument. Preserve the original shared-objects prefix inside the copied environment, so unchanged external objects and companions resolve exactly as in standing run-joint.'),indent=2)+'\n');print('verified private environment',len(checked),'external objects; removed own links',len(removed))

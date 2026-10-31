from pathlib import Path
import json,hashlib,re,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');B=H.parent/'codex-pv-b3p6-20261028';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();bad=[]
external=json.loads((B/'external-object-manifest.json').read_text());env=json.loads((H/'env-J-private.json').read_text());roots=[H/'lean-objects']+[Path(s)for s in env['LEAN_PATH'].split(':')]
def resolve(m):
 rel=Path(m.replace('.','/')+'.olean')
 if '.'in m:
  root=next((r for r in roots if (r/m.split('.')[0]).is_dir()),None)
  return root/rel if root else None
 return next((r/rel for r in roots if(r/rel).exists()),None)
for r in external:
 m=r['module'].replace('/','.');p=resolve(m)
 if p is None or not p.exists()or sha(p)!=r['object_sha256']:bad.append(dict(kind='external',module=m,resolved=str(p),expected=r['object_sha256']))
old=json.loads((H/'cache-verification.json').read_text())['objects']
for m,r in old.items():
 p=resolve(m);expected=r.get('object_sha256',r.get('sha256'))
 if p is None or not p.exists()or sha(p)!=expected:bad.append(dict(kind='inherited',module=m,resolved=str(p),expected=expected))
manifest=json.loads((H/'frozen-manifest.json').read_text());accepted=[]
for r in manifest['focused']:
 src=H/'lean'/(r['module']+'.lean');p=resolve(r['module']);assert sha(src)==r['sha256'],('source changed',r['module'])
 receipt=json.loads((H/f"lean-{r['attempt']}"/'receipt/receipt.json').read_text());assert receipt['exit_status']==0
 for dep,d in receipt['dependency_objects'].items():
  q=resolve(dep)
  if q is None or not q.exists()or sha(q)!=d['sha256']:bad.append(dict(kind='dependency changed',consumer=r['module'],module=dep,resolved=str(q),expected=d['sha256']))
 accepted.append(dict(module=r['module'],source_sha256=sha(src),object=str(p),object_sha256=sha(p),companions={str(q):sha(q)for q in p.parent.glob(p.stem+'.*')}))
marker=H.parent/'QUIET_WINDOW.json';quiet=dict(epoch=time.time(),marker=json.loads(marker.read_text())if marker.exists()else None,mtime_ns=marker.stat().st_mtime_ns if marker.exists()else None)
x=dict(source_revision=(H/'revision').read_text().strip(),external_count=len(external),inherited_count=len(old),accepted=accepted,first_namespace_root_resolution=True,mismatches=bad,quiet_window=quiet,prior_quiet_snapshot_limitation='Before wrapper update, explicit per-run marker snapshots were not retained; outer/inner admission JSON and timestamps are retained. This snapshot is supplemental, not retroactive contemporaneous evidence.')
(H/'preaudit-verification.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(external=len(external),inherited=len(old),accepted=len(accepted),mismatches=bad)));assert not bad,bad

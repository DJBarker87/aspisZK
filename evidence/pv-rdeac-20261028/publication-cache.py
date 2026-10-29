from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');x=json.loads((D/'publication-inputs.json').read_text());O=D/'objects'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
E=json.loads((D/'env-J.json').read_text());roots=[O]+list(map(Path,E['LEAN_PATH'].split(':')))
rows=[];failed=[]
byname={r['module']:r for r in x['modules']}
for m in x['order']:
 r=byname[m]
 if m==x['root']:continue
 expected=x['expected'][m];p=Path(expected['path']);source=D.parent/'aspis-joint-20261019/sources'/(m.replace('.','/')+'.lean')
 row=dict(module=m,expected_object_sha256=expected['sha256'],object=str(p),source=str(source),expected_source_sha256=r['source_sha256'],receipt=r['receipt'],deps=[])
 row['object_sha256']=sha(p) if p.exists() else None;row['source_sha256']=sha(source) if source.exists() else None
 row['ok']=row['object_sha256']==row['expected_object_sha256'] and row['source_sha256']==row['expected_source_sha256']
 for dep,d in r['record']['dependency_objects'].items():
  rel=dep.replace('.','/')+'.olean';q=next((root/rel for root in roots if (root/rel).is_file()),None)
  # Not linked yet: the recorded object in this same pending coherent cohort.
  if q is None and dep in x['expected']:q=Path(x['expected'][dep]['path'])
  actual=sha(q) if q and q.exists() else None
  row['deps'].append(dict(module=dep,path=str(q),actual=actual,expected=d['sha256'],ok=actual==d['sha256']))
  row['ok'] &= actual==d['sha256']
 rows.append(row)
 if not row['ok']:failed.append(row)
 else:
  q=O/(m.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==row['object_sha256'],m
  else:q.symlink_to(p)
  for suffix in ['.private','.server']:
   a=Path(str(p)+suffix);b=Path(str(q)+suffix)
   if a.is_file() and not b.exists():b.symlink_to(a)
result=dict(rows=rows,failed=failed,ok=not failed,toolchain=E['LEAN_GITHASH'],original_env='J, recorded in each original capped run target; external import cone byte-equals preverified 5673-object authority',reuse_boundary='complete project transitive imports checked above; no shared files modified')
(D/'publication-cache.json').write_text(json.dumps(result,indent=2)+'\n');print('reusable',len(rows)-len(failed),'failed',[(r['module'],[(d['module'],d['ok']) for d in r['deps'] if not d['ok']]) for r in failed]);assert not failed

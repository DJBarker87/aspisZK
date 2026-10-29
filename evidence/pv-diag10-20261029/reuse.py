from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029');P=D.parent/'codex-pv-diag9-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows={}
for name in ['reuse.json','decoder-reuse.json']:
 data=json.loads((P/name).read_text())
 for m,r in data['rows'].items():
  p=P/'objects'/(m.replace('.','/')+'.olean')
  expected=r['object_sha256'];assert sha(p)==expected,m
  src=Path(r.get('source_path',str(D.parent/'codex-pv-rj4idb-20261029/sources'/(m.replace('.','/')+'.lean'))))
  assert sha(src)==r['source_sha256'],m
  for dep in r.get('dependencies',[]) if isinstance(r.get('dependencies'),list) else []:
   assert sha(Path(dep['path']))==dep['expected']
  rows[m]=dict(path=str(p),sha256=expected,source=str(src),source_sha256=sha(src))
  q=D/'objects'/(m.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
  for a,b in [(p,q),(Path(str(p)+'.private'),Path(str(q)+'.private')),(Path(str(p)+'.server'),Path(str(q)+'.server')),(p.with_suffix('.ir'),q.with_suffix('.ir'))]:
   if a.exists() and not b.exists():b.symlink_to(a)
(D/'reuse.json').write_text(json.dumps(dict(rows=rows,checked=len(rows),authority='diag9 accepted recursively fingerprinted cohort; candidate source identity separately checked'),indent=2)+'\n')
print('checked',len(rows))

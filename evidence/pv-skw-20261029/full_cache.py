from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029');P=D.parent/'codex-pv-l1g-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((P/'CACHE-PIN.json').read_text());assert sha(D/'l1g-final-validation.json')==pin['final_validation_sha256']
h6=json.loads((D/'l1g-final-validation.json').read_text())['h6_final']
assert h6['all_match']
rows=[]
for r in h6['checks']:
 p=Path(r['path']);assert sha(p)==r['sha256'],r['module'];rows.append(r)
for r in rows:
 p=Path(r['path']);q=D/'objects'/(r['module'].replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==r['sha256'],('private conflict',r['module'])
 for src,dst in [(p,q),(Path(str(p)+'.server'),Path(str(q)+'.server')),(Path(str(p)+'.private'),Path(str(q)+'.private')),(p.with_suffix('.ir'),q.with_suffix('.ir'))]:
  if src.is_file() and not dst.exists():dst.symlink_to(src)
(D/'full-cache-verification.json').write_text(json.dumps(dict(checks=len(rows),source_pin=pin,old_dependency_edges=h6['dependency_edges'],all_match=True,reason='Lean dynamic server/tactic imports require retained complete package prefixes'),indent=2)+'\n')
print('all',len(rows),'retained source/object pins checked and staged')

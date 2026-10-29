from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag6-20261029');P=D.parent/'codex-pv-diag3-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((P/'resume-cache-preflight.json').read_text())['rows'];pins=json.loads((P/'project-resolution.json').read_text())['modules'];seen={}
def visit(m):
 if m in seen:return
 q=r[m];p=Path(q['path']);assert sha(p)==q['sha256'],m
 if m in pins:assert q['source_sha256']==pins[m]['sha256'],m
 seen[m]=q
 for dep,v in q.get('record_dependencies',{}).items():
  assert r[dep]['sha256']==v['sha256'],(m,dep)
  visit(dep)
visit('R0Z.FsAbortBounds')
for m,q in seen.items():
 if m not in pins:continue
 p=Path(q['path']);dst=D/'objects'/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists();dst.symlink_to(p)
 for a,b in [(Path(str(p)+'.server'),Path(str(dst)+'.server')),(Path(str(p)+'.private'),Path(str(dst)+'.private')),(p.with_suffix('.ir'),dst.with_suffix('.ir'))]:
  if a.is_file():b.symlink_to(a)
(D/'law-preflight.json').write_text(json.dumps(dict(checked=len(seen),rows=seen,source_authority='diag3 project-resolution EJR/h5 pins, read-only h6 cache; original env-J external authority',environment=json.loads((D/'env-J.json').read_text()),mismatches=[]),indent=2)+'\n');print('law closure',len(seen),'project',len(set(seen)&set(pins)))

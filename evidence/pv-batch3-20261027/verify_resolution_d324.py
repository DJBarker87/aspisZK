from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
search=[Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects')]+list(map(Path,e['LEAN_PATH'].split(':')))
rows=json.loads((H/'d324-external-object-manifest.json').read_text());bad=[];checked=[]
for r in rows:
 q=next((p/(r['module']+'.olean') for p in search if (p/(r['module']+'.olean')).is_file()),None)
 h=hashlib.sha256(q.read_bytes()).hexdigest() if q else None
 v=dict(module=r['module'],selected_path=str(q),expected=r['object_sha256'],actual=h,match=h==r['object_sha256'])
 checked.append(v)
 if not v['match']:bad.append(v)
(H/'d324-resolution-verification.json').write_text(json.dumps(dict(search=list(map(str,search)),checked_count=len(checked),mismatches=bad,objects=checked),indent=1)+'\n')
print(json.dumps(dict(checked=len(checked),mismatches=bad)))

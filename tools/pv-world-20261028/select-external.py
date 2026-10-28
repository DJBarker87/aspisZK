"""Populate only this job's import cache from h4-pinned external objects.
Lean can stop at a dangling symlink in an earlier LEAN_PATH prefix. This
private prefix makes the verified selections explicit; no shared file changes.
"""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
manifest=json.loads((E/'external-object-manifest.json').read_text())
code='''from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-world-20261028')
rows=[]
for x in MANIFEST:
 a=Path(x['path']);assert hashlib.sha256(a.read_bytes()).hexdigest()==x['object_sha256'],str(a)
 p=D/'lean-objects'/(x['module']+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink() or p.exists():assert hashlib.sha256(p.read_bytes()).hexdigest()==x['object_sha256'],str(p)
 else:p.symlink_to(a)
 companions={}
 for suffix in ['.server','.private','.ir']:
  source=a.with_suffix('.ir') if suffix == '.ir' else Path(str(a)+suffix)
  dest=p.with_suffix('.ir') if suffix == '.ir' else Path(str(p)+suffix)
  if source.exists():
   h=hashlib.sha256(source.read_bytes()).hexdigest()
   if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==h
   else:dest.symlink_to(source)
   companions[suffix]=dict(path=str(source),sha256=h)
 rows.append(dict(module=x['module'],selected_path=str(p),authority_path=str(a),sha256=x['object_sha256'],companions=companions))
print(json.dumps(dict(ok=True,mode='private read-only h4 object links; no external/project rebuild or shared mutation',rows=rows)))
'''.replace('MANIFEST',repr(manifest))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'private-external-selection.json').write_text(json.dumps(j,indent=2)+'\n')
print('Pinned private external object selections:',len(j['rows']))

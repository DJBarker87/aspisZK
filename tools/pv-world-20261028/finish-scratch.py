"""Inventory then remove only this job's rebuildable compiled artifacts.
No keys, source inputs, receipts, shared objects or reused targets are removed.
"""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
code='''from pathlib import Path
import hashlib,json
root=Path('/home/dombarker/project-offloads/codex-pv-world-20261028/lean-objects')
assert root.is_dir() and not root.is_symlink()
files=sorted(p for p in root.rglob('*') if p.is_file() or p.is_symlink())
rows=[]
for p in files:
 assert p.suffix in ['.olean','.server','.private','.ir','.ilean'],str(p)
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 rows.append(dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest(),symlink=p.is_symlink(),retained_target=str(p.resolve()) if p.is_symlink() else None))
manifest=root.parent/'resume-private-object-manifest.json'
manifest.write_text(json.dumps(rows,indent=2)+'\\n')
# unlink removes the private directory entry, never a reused symlink target.
for p in files:p.unlink()
for p in sorted((p for p in root.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True):
 assert not p.is_symlink(),str(p)
 p.rmdir()
root.rmdir()
print(json.dumps(dict(manifest_path=str(manifest),manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),objects=rows,cleanup=dict(removed_entries=len(files),reused_targets_removed=0,keys_touched=False,sources_and_receipts_retained=True))))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout)
(E/'resume-private-object-manifest.json').write_text(json.dumps(j['objects'],indent=2)+'\n')
(E/'resume-cleanup.json').write_text(json.dumps({k:v for k,v in j.items() if k!='objects'},indent=2)+'\n')
print(json.dumps(j['cleanup']))

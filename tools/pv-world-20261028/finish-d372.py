"""Inventory this job's object scratch, retain hashes, then unlink private entries.
Full external/reused manifests stay on the host; no source, receipt or key deletion.
"""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
code='''from pathlib import Path
import hashlib,json
root=Path('/home/dombarker/project-offloads/codex-pv-world-20261028/lean-objects')
assert root.is_dir() and not root.is_symlink()
files=sorted(p for p in root.rglob('*') if p.is_file() or p.is_symlink())
rows=[];owned={};dangling=0
for p in files:
 assert p.suffix in ['.olean','.server','.private','.ir','.ilean'],str(p)
 link=p.is_symlink();exists=p.exists();h=hashlib.sha256()
 if exists:
  with p.open('rb') as f:
   for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 else:dangling+=1
 row=dict(path=str(p),bytes=p.stat().st_size if exists else None,sha256=h.hexdigest() if exists else None,symlink=link,retained_target=str(p.resolve()) if link else None)
 rows.append(row)
 if not link and p.suffix=='.olean':owned[str(p.relative_to(root))[:-6].replace('/','.')]=dict(bytes=row['bytes'],object_sha256=row['sha256'])
manifest=root.parent/'d372-private-object-manifest.json';manifest.write_text(json.dumps(rows,indent=2)+'\\n')
for p in files:p.unlink()
for p in sorted((p for p in root.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True):
 assert not p.is_symlink();p.rmdir()
root.rmdir()
print(json.dumps(dict(full_manifest_host_path=str(manifest),full_manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),full_manifest_bytes=manifest.stat().st_size,removed_entries=len(files),dangling_links=dangling,reused_targets_removed=0,keys_touched=False,sources_and_receipts_retained=True,private_modules=owned)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'d372-cleanup.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({k:v for k,v in j.items() if k!='private_modules'}))

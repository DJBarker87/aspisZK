from pathlib import Path
import os,json,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');rows=json.loads((T/'EJS_provider-sources.json').read_text());repairs=[]
for r in rows:
 p=Path(r['host_path'])
 if p.is_symlink():
  source=p.resolve();before=hashlib.sha256(p.read_bytes()).hexdigest();assert before==r['source_sha256'];p.unlink();os.link(source,p)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==before
  repairs.append(dict(path=str(p),unchanged_sha256=before,original=str(source),representation='hardlink; no bytes copied or edited'))
(T/'EJS_provider-path-repair.json').write_text(json.dumps(dict(reason='31012 rejected symlink canonical input path outside Lean -R root before elaboration. Hardlinks retain identical bytes/inode but a path inside the source root. This is a changed loader context, not an unchanged proof retry.',repairs=repairs),indent=2)+'\n')
print('loader paths repaired',len(repairs))

"""Bind existing read-only proof objects in this job's private R1Z cache.
Lean chooses a package directory before an individual module, so an appended
cache cannot supply a missing R1Z module. No source or existing object is edited.
"""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
shared=Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects/R1Z')
cohort=Path('/home/dombarker/project-offloads/codex-pv-op134-20261027/objects/R1Z')
root=H/'reference-objects';dest=root/'R1Z';dest.mkdir(parents=True,exist_ok=False)
files={p.name:p for p in shared.iterdir() if p.is_file() and ('.olean' in p.name or p.suffix in ['.ilean','.ir'])}
added=[];differences=[]
for p in cohort.iterdir():
 if not p.is_file() or not ('.olean' in p.name or p.suffix in ['.ilean','.ir']):continue
 if p.name not in files:files[p.name]=p;added.append(p.name)
 elif hashlib.sha256(files[p.name].read_bytes()).digest()!=hashlib.sha256(p.read_bytes()).digest():differences.append(p.name)
for name,p in files.items():(dest/name).symlink_to(p)
rec={'kind':'private read-only proof-cache binding; not a source/object rebuild','shared_sources_written':False,'shared_objects_written':False,'private_directory':str(root),'bindings':{n:str(p) for n,p in files.items()},'cohort_additions':added,'differing_duplicate_names':differences}
(H/'reference-cache-bindings.json').write_text(json.dumps(rec,indent=2)+'\n');print({'bindings':len(files),'cohort_additions':len(added),'differing_duplicate_names':differences})

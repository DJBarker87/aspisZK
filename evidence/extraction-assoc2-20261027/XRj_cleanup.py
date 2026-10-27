"""Remove only this terminal job's rebuildable caches after recording hashes."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc2-20261027')
assert B.name=='codex-cx-extraction-assoc2-20261027'
live=[]
for p in Path('/proc').glob('[0-9]*/cmdline'):
 try:args=p.read_bytes().split(b'\0')
 except (PermissionError,FileNotFoundError,ProcessLookupError):continue
 if not args or int(p.parent.name)==os.getpid():continue
 exe=Path(args[0].decode(errors='replace')).name
 cmd=b' '.join(args).decode(errors='replace')
 if exe in ['lean','lake','cargo','cargo-kani','kani','cbmc','cadical','rustc'] and str(B) in cmd:live.append({'pid':p.parent.name,'command':cmd})
assert not live,live
rows=[]
for root in ['XRj_objects','XRj_target','.lake']:
 d=B/root
 if not d.exists():continue
 count=0;size=0;objects=[]
 for p in d.rglob('*'):
  if p.is_file():
   n=p.stat().st_size;size+=n;count+=1
   if root=='XRj_objects':objects.append({'path':str(p.relative_to(B)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':n})
 rows.append({'path':root,'files':count,'bytes':size,'objects':objects})
 shutil.rmtree(d)
# Crate contains symlinks to retained source files, not keys or source originals.
d=B/'XRj_crate'
if d.exists():
 assert all(p.is_symlink() or p.name in ['Cargo.lock'] for p in d.iterdir())
 shutil.rmtree(d)
receipt={'live_own_build_processes':live,'removed_caches':rows,'failed_Funs_object_existed':any(x['path'].endswith('/Funs.olean') for r in rows for x in r['objects']),'solver_temps':'No solver temp filename is emitted by K007; ownership of unrelated /tmp files is unproven, so none are deleted. No live own solver remains.','keys':'No keys or wallet directories accessed; only explicit rebuildable caches and crate symlinks removed.'}
(B/'XRj_cleanup.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'removed_bytes':sum(r['bytes'] for r in rows),'failed_Funs_object_existed':receipt['failed_Funs_object_existed']}))

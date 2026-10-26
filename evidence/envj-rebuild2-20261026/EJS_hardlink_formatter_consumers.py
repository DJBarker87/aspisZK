from pathlib import Path
import os,json,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');records=[]
for name in ['EJS_formatter_joint','EJS_formatter_union']:
 for p in (U/name/'objects').rglob('*'):
  if p.is_symlink() and p.is_file():
   source=p.resolve();h=hashlib.sha256(p.read_bytes()).hexdigest();p.unlink();os.link(source,p);records.append(dict(path=str(p),source=str(source),sha256=h))
(T/'EJS_formatter-loader-repair.json').write_text(json.dumps(dict(reason='31021 probe confirms repaired Formatter and unwrap have no axioms after library aliases become hardlinks. Extend root-preserving object bindings to generated dependency namespaces before two consumer replays.',bindings=records),indent=2)+'\n');print('consumer bindings',len(records))

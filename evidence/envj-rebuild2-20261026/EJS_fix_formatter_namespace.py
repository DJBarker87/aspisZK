from pathlib import Path
import json,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');records=[]
for name in ['EJS_formatter_joint','EJS_formatter_union']:
 for module in ['Aeneas','AeneasMeta']:
  for ext in ['.olean','.olean.private','.olean.server','.ir']:
   src=J/'objects'/(module+ext);dest=U/name/'objects'/(module+ext)
   if src.is_file() and not dest.exists():dest.symlink_to(src.resolve());records.append(dict(path=str(dest),source=str(src.resolve()),sha256=hashlib.sha256(dest.read_bytes()).hexdigest()))
(T/'EJS_formatter-loader-repair.json').write_text(json.dumps(dict(reason='31018 lacked root Aeneas.olean after adding the local Aeneas namespace directory. Bind exact retained umbrella companions in both profiles; source bytes remain unchanged.',bindings=records),indent=2)+'\n');print('bound',len(records))

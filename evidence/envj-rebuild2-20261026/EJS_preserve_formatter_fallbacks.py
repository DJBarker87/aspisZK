from pathlib import Path
import json,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');records=[]
for name in ['EJS_formatter_joint','EJS_formatter_union']:
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  p=U/name/'objects'/('AspisV8R19/SamplerWordRead'+ext)
  if p.exists() or p.is_symlink():
   dest=U/name/'EJS_retained-fallback'/('SamplerWordRead'+ext);dest.parent.mkdir(exist_ok=True);assert not dest.exists()
   h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None;p.rename(dest);records.append(dict(path=str(p),retained=str(dest),sha256=h))
p=T/'EJS_formatter-loader-repair.json';d=json.loads(p.read_text());d['retained_fallbacks']=records;p.write_text(json.dumps(d,indent=2)+'\n');print('retained fallbacks',len(records))

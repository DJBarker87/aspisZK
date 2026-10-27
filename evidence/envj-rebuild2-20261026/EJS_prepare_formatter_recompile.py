from pathlib import Path
import json,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');records=[]
for name in ['EJS_formatter_joint','EJS_formatter_union']:
 root=U/name
 for m in ['AspisR72Sampler/Types','AspisR72Sampler/Funs','AspisV8R19/SamplerWordRead']:
  for ext in ['.olean','.olean.private','.olean.server','.ir']:
   p=root/'objects'/(m+ext)
   if p.exists() or p.is_symlink():
    dest=root/'EJS_before-recompile'/(m+ext);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None;p.rename(dest);records.append(dict(path=str(p),retained=str(dest),sha256=h))
p=T/'EJS_formatter-loader-repair.json';d=json.loads(p.read_text());d['recompile_reason']='31022/31023 still retain Formatter through cached generated imports despite direct library probe. Recompile both exact Types/Funs source profiles against the repaired owner; invalidate reuse for this changed transitive context.';d['before_recompile']=records;d['actual_repaired_Fmt_objects']={n:hashlib.sha256((U/n/'objects/Aeneas/Std/Core/Fmt.olean').read_bytes()).hexdigest() for n in ['EJS_formatter_joint','EJS_formatter_union']};p.write_text(json.dumps(d,indent=2)+'\n');print('retained',len(records),'output aliases before source-identical dependency rebuild')

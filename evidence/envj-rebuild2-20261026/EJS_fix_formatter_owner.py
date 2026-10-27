from pathlib import Path
import json,hashlib,os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');root=U/'EJS_formatter_union';records=[];owner=[]
for ext in ['.olean','.olean.private','.olean.server','.ir']:
 src=U/'EJS_formatter_joint/objects'/('Aeneas/Std/Core/Fmt'+ext);dest=root/'objects'/('Aeneas/Std/Core/Fmt'+ext)
 if not src.is_file():continue
 new=hashlib.sha256(src.read_bytes()).hexdigest();old=hashlib.sha256(dest.read_bytes()).hexdigest() if dest.is_file() else None
 if old!=new:
  retained=root/'EJS_old-Fmt-owner'/('Fmt'+ext);retained.parent.mkdir(exist_ok=True)
  if dest.exists() or dest.is_symlink():dest.rename(retained)
  os.link(src,dest)
 owner.append(dict(path=str(dest),previous_sha256=old,repaired_sha256=new,source=str(src)))
for m in ['Aeneas','Aeneas/Std','Aeneas/Std/Core','Aeneas/Std/Array','Aeneas/Std/Array/ArraySlice','ImportUnionNamedDiscriminant','AspisR72Sampler/Types','AspisR72Sampler/Funs','AspisV8R19/SamplerWordRead']:
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  p=root/'objects'/(m+ext)
  if p.exists() or p.is_symlink():
   dest=root/'EJS_before-owner-rebuild'/(m+ext);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None;p.rename(dest);records.append(dict(path=str(p),retained=str(dest),sha256=h))
p=T/'EJS_formatter-loader-repair.json';d=json.loads(p.read_text());d['root_cause']='Canonical mirror replaced valid reuse symlinks with earlier fallback cache objects. Union Fmt had cd6de4ce... instead of compiled repair 438c263b...; joint regular file retained the repair. EJS adapter now preserves valid symlinks. No canonical launcher file edited.';d['owner_repair']=owner;d['owner_rebuild_retained']=records;p.write_text(json.dumps(d,indent=2)+'\n');print('fixed owner; retained',len(records),'union dependent outputs')

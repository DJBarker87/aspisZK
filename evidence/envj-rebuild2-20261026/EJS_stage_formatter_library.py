from pathlib import Path
import json,hashlib,base64
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');rows=json.loads((T/'EJS_formatter-sources.json').read_text());staged=[]
for name in ['EJS_formatter_joint','EJS_formatter_union']:
 root=U/name
 for source in json.loads((T/'EJS_formatter-library-payload.json').read_text())['rows']:
  r=source.copy();b=base64.b64decode(r.pop('source_base64'));assert hashlib.sha256(b).hexdigest()==r['source_sha256'];src=root/'sources'/(r['module']+'.lean');src.parent.mkdir(parents=True,exist_ok=True);assert not src.exists();src.write_bytes(b);r.update(workspace=name,host_path=str(src));rows.append(r)
 for m in ['Aeneas','Aeneas/Std','Aeneas/Std/Core','Aeneas/Std/Array','Aeneas/Std/Array/ArraySlice','AspisR72Sampler/Types','AspisR72Sampler/Funs','AspisV8R19/SamplerWordRead']:
  for ext in ['.olean','.olean.private','.olean.server','.ir']:
   p=root/'objects'/(m+ext)
   if p.exists() or p.is_symlink():
    dest=root/'EJS_before-library-rebuild'/(m+ext);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None;p.rename(dest);staged.append(dict(source=str(p),retained=str(dest),sha256=h))
(T/'EJS_formatter-sources.json').write_text(json.dumps(rows,indent=2)+'\n')
p=T/'EJS_formatter-loader-repair.json';d=json.loads(p.read_text());d['full_library_rebuild_reason']='31024–31029 generated dependency-only replay retained legacy Formatter. Apply entire recorded six-module repair owner profile, recompiling five additional source-identical library modules before generated dependencies and consumers.';d['before_library_rebuild']=staged;p.write_text(json.dumps(d,indent=2)+'\n');print('staged ten library sources; retained',len(staged),'outputs')

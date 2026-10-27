from pathlib import Path
import json,os,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');root=U/'EJS_formatter_union';base=json.loads((T/'EJR_all-restored-sources.json').read_text());r=next(r for r in base if r['module']=='ImportUnionNamedDiscriminant' and r['workspace']=='union').copy();src=root/'sources/ImportUnionNamedDiscriminant.lean';assert not src.exists();os.link(r['host_path'],src);assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256'];r.update(workspace='EJS_formatter_union',host_path=str(src));rows=json.loads((T/'EJS_formatter-sources.json').read_text());rows.append(r);(T/'EJS_formatter-sources.json').write_text(json.dumps(rows,indent=2)+'\n');retained=[]
for m in ['ImportUnionNamedDiscriminant','AspisR72Sampler/Types','AspisR72Sampler/Funs','AspisV8R19/SamplerWordRead']:
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  p=root/'objects'/(m+ext)
  if p.exists() or p.is_symlink():
   dest=root/'EJS_before-named-rebuild'/(m+ext);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None;p.rename(dest);retained.append(dict(path=str(p),retained=str(dest),sha256=h))
p=T/'EJS_formatter-loader-repair.json';d=json.loads(p.read_text());d['union_named_rebuild_reason']='Joint consumer 31044 passes. Union consumer 31045 still imports historical ImportUnionNamedDiscriminant built over a different umbrella; recompile that exact source and union-only dependents. Joint success is not rerun.';d['named_retained']=retained;p.write_text(json.dumps(d,indent=2)+'\n');print('named source staged; retained',len(retained))

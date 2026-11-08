"""Exact retained metadata excerpts; no semantic defaults are filled in."""
from pathlib import Path
import hashlib,json,lzma
E=Path('evidence/pv-lib-20261107/lane-A/session8');src=E.parent/'session5/thread-llbc.json.xz';raw=lzma.decompress(src.read_bytes());p=json.loads(raw)['translated'];d={}
def walk(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:i,v=x['HashConsedValue'];d[i]=v
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(p)
def norm(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:return norm(x['HashConsedValue'][1])
  if 'Deduplicated'in x:return norm(d[x['Deduplicated']])
  return {k:norm(v)for k,v in x.items()}
 if isinstance(x,list):return list(map(norm,x))
 return x
native=E.parent/'session7/NativeInstructions.json.xz';nraw=lzma.decompress(native.read_bytes());n=json.loads(nraw)
r=dict(input=str(src),compressed_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),raw_sha256=hashlib.sha256(raw).hexdigest(),
       native_input=str(native),native_sha256=hashlib.sha256(nraw).hexdigest(),
       Arc_type=dict(id=21,generics=p['type_decls'][21]['generics'],fields=[dict(name=f['name'],type=norm(f['ty']))for f in p['type_decls'][21]['kind']['Struct']]),
       Arc_Destruct_impl=dict(id=76,generics=p['trait_impls'][76]['generics'],methods=norm(p['trait_impls'][76]['methods'])),
       allocator_marker=norm(d[35850]),bound_dyn_type_variable=d[350],
       retained_raw_function_bodies={str(i):p['fun_decls'][i]['body'] if isinstance(p['fun_decls'][i]['body'],str) else 'Structured'for i in [157,248,405,486,584,608,644,661]},
       emitted_body_kinds={str(i):next(f['code'].get('opcode','Structured')for f in n['functions']if f['function']==i)for i in [157,248,405,486,584,608,644,661]},
       distinction='The amended native emission supplies precise structured glue405 while the retained raw LLBC declaration is opaque. Syntax identity with that accepted emission is recorded; no new Rust/binary refinement credit is inferred.',
       allocation_byte_images_defined=0,D991='No total byte image or initialized value for unwritten bytes is defined. Existing inherited total-image results are not promoted to source adequacy.')
(E/'METADATA_PROVENANCE.json').write_text(json.dumps(r,indent=2)+'\n')

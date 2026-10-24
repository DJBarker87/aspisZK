#!/usr/bin/env python3
"""Read-only core/job dependency closure; never inspect another owner's caches."""
import hashlib,json,pathlib,re
T=pathlib.Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0')
def closure(modules, source_dir, object_dir):
 seen={};paths={}
 def add_file(p):
  if p.is_file():paths[str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
 def visit(name):
  if name in seen:return
  own=name.startswith('Port22ARENA_')
  stem=(object_dir if own else T/'lib/lean')/name.replace('.','/')
  src=(source_dir if own else T/'src/lean')/(name.replace('.','/')+'.lean')
  obj=stem.with_suffix('.olean');assert obj.is_file(),obj
  if own:
   assert src.is_file();imports=re.findall(r'^import (\S+)',src.read_text(),re.M)
  else:
   meta=stem.with_suffix('.ilean');assert meta.is_file(),meta
   imports=[r[0] for r in json.loads(meta.read_text())['directImports']]
  seen[name]=dict(source=str(src),object=str(obj),directImports=imports)
  add_file(src)
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:add_file(stem.with_suffix(suffix))
  for imp in imports:visit(imp)
 for name in modules:visit(name)
 for p in sorted((T/'lib').glob('*.dylib')):add_file(p)
 add_file(T/'bin/lean')
 return dict(modules=seen,files=paths,fingerprint=hashlib.sha256(json.dumps(paths,sort_keys=True).encode()).hexdigest())
def verify(snapshot):
 for name,item in snapshot['files'].items():
  p=pathlib.Path(name);assert p.stat().st_size==item['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],name

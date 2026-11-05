"""Retain byte-exact attempt inputs once per SHA256; index original paths."""
from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;D=E/'NGL_INPUTS';D.mkdir(exist_ok=True)
p=E/'NGL_INPUTS.json';manifest=json.loads(p.read_text()) if p.exists() else {'schema':1,'objects':{},'attempts':{}}
for a in E.iterdir():
 if not a.is_dir() or not re.fullmatch('NGL_[KLE][0-9]{3}',a.name):continue
 root=a/'sources'
 if not root.exists():continue
 paths=manifest['attempts'].setdefault(a.name,{})
 for f in root.rglob('*'):
  if not f.is_file():continue
  raw=f.read_bytes();sha=hashlib.sha256(raw).hexdigest();q=D/(sha+'.xz')
  if q.exists():assert lzma.decompress(q.read_bytes())==raw
  else:q.write_bytes(lzma.compress(raw,preset=6))
  rel=str(f.relative_to(root));assert rel not in paths or paths[rel]==sha
  paths[rel]=sha;manifest['objects'][sha]={'path':str(q.relative_to(E)),'bytes':len(raw),'archive_sha256':hashlib.sha256(q.read_bytes()).hexdigest()};f.unlink()
 for d in sorted(root.rglob('*'),key=lambda x:len(x.parts),reverse=True):
  if d.is_dir():d.rmdir()
 root.rmdir()
p.write_text(json.dumps(manifest,indent=1)+'\n')
raw=[]
for f in (E/'NGL_extracted').rglob('*Template.lean'):
 b=f.read_bytes();f.with_name(f.name+'.xz').write_bytes(lzma.compress(b));f.with_name(f.name+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');raw.append({'path':str(f.relative_to(E)),'sha256':hashlib.sha256(b).hexdigest(),'admitted':False,'reason':'raw extraction scaffolding, never compiled or imported'});f.unlink()
if raw:(E/'NGL_RAW_TEMPLATES.json').write_text(json.dumps(raw,indent=1)+'\n')
print(json.dumps({'unique_inputs':len(manifest['objects']),'attempt_input_sets':len(manifest['attempts']),'unique_raw_bytes':sum(x['bytes'] for x in manifest['objects'].values())}))

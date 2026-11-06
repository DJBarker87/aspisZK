"""Retain each repeated immutable snapshot/metadata input once by its content hash."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;pool=E/'NJS_inputs';pool.mkdir(exist_ok=True)
manifest=E/'NJS_POOLED_INPUTS.json';refs=json.loads(manifest.read_text()) if manifest.exists() else {}
files=[q for q in E.glob('NJS_*/sources/**/*') if q.is_file()]
files += [q for d in E.glob('NJS_*_validation') for q in d.glob('metadata*') if q.is_file() and not q.name.endswith('.sha256')]
for q in files:
 name=str(q.relative_to(E));data=q.read_bytes();side=None
 if q.name.endswith('.xz') and q.with_name(q.name[:-3]+'.sha256').exists():
  side=q.with_name(q.name[:-3]+'.sha256');data=lzma.decompress(data);assert hashlib.sha256(data).hexdigest()==side.read_text().strip();name=name[:-3]
 h=hashlib.sha256(data).hexdigest();dest=pool/(h+'.xz')
 if not dest.exists():dest.write_bytes(lzma.compress(data,preset=6))
 assert lzma.decompress(dest.read_bytes())==data
 refs[name]={'sha256':h,'bytes':len(data),'pool':str(dest.relative_to(E))};q.unlink()
 if side:side.unlink()
manifest.write_text(json.dumps(refs,indent=1)+'\n')
print('pooled',len(refs),'immutable input paths into',len(list(pool.glob('*.xz'))),'unique hashes')

"""Lossless deduplication of receipt inputs; retain every consumed byte."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
canonical={}
for p in E.iterdir():
 if p.is_file() and p.name not in ['NJZ_native.rs'] and not p.name.endswith('.log'):
  canonical.setdefault(sha(p.read_bytes()),dict(file=p.name))
payloads={}
for name,text in json.load(open(E/'NJZ_NATIVE_INPUTS.json')).items():payloads[sha(text.encode())]=dict(payload='NJZ_NATIVE_INPUTS.json',key=name)
index=json.load(open(E/'NJZ_INPUT_INDEX.json')) if (E/'NJZ_INPUT_INDEX.json').exists() else {};objects=E/'NJZ_INPUT_OBJECTS';objects.mkdir(exist_ok=True);total=0
for p in sorted(E.glob('NJZ_[LKE][0-9][0-9][0-9]/sources/**/*')):
 if not p.is_file():continue
 raw=p.read_bytes();h=sha(raw);item=dict(sha256=h,bytes=len(raw));total+=len(raw)
 if h in payloads:item.update(payloads[h])
 elif h in canonical:item.update(canonical[h])
 else:
  obj=objects/(h+'.xz')
  if not obj.exists():obj.write_bytes(lzma.compress(raw,preset=6))
  assert lzma.decompress(obj.read_bytes())==raw
  item['archive']=str(obj.relative_to(E))
 index[str(p.relative_to(E))]=item
E.joinpath('NJZ_INPUT_INDEX.json').write_text(json.dumps(index,indent=2)+'\n')
for name,item in index.items():
 if 'archive' in item:raw=lzma.decompress(E.joinpath(item['archive']).read_bytes())
 elif 'payload' in item:raw=json.load(open(E/item['payload']))[item['key']].encode()
 else:raw=E.joinpath(item['file']).read_bytes()
 assert sha(raw)==item['sha256'] and len(raw)==item['bytes'],name
 E.joinpath(name).unlink(missing_ok=True)
for p in sorted(E.glob('NJZ_[LKE][0-9][0-9][0-9]/sources/**/*'),key=lambda p:len(p.parts),reverse=True):
 if p.is_dir() and not list(p.iterdir()):p.rmdir()
# Canonical source remains in patch/payload and receipt input index, never shipped.
p=E/'NJZ_native.rs'
if p.exists():
 assert sha(p.read_bytes()) in payloads;p.unlink()
E.joinpath('NJZ_INPUT_PACKING.json').write_text(json.dumps(dict(status='PASS',capture_paths=len(index),raw_bytes=total,compressed_objects=len(list(objects.glob('*.xz'))),all_inputs_lossless=True,canonical_payload='NJZ_NATIVE_INPUTS.json',canonical_patch='NJZ_native.patch'),indent=2)+'\n')
print(f'Input packing PASS: {len(index)} captures retained losslessly; {len(list(objects.glob("*.xz")))} unique old-input objects.')

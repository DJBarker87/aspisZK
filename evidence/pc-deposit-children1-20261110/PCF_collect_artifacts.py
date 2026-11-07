"""Stream raw text evidence and verify pinned immutable input bytes."""
from pathlib import Path
import json,hashlib,lzma
B=Path.cwd();C=B.parent/'codex-pc-deposit-children1-cache-20261110';D=B/'PCF_RAW_FINAL';D.mkdir(exist_ok=True)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
manifest=[]
for p in sorted(B.glob('PCF_NEP_*')):
 if not p.is_file():continue
 h=hashlib.sha256();out=D/(p.name+'.xz')
 with p.open('rb') as f,lzma.open(out,'wb',preset=6) as g:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b);g.write(b)
 (D/(p.name+'.sha256')).write_text(h.hexdigest()+'\n')
 manifest.append(dict(source=p.name,uncompressed_sha256=h.hexdigest(),uncompressed_bytes=p.stat().st_size,compressed_sha256=sha(out),compressed_bytes=out.stat().st_size))
pins=json.loads(lzma.decompress((B/'PCF_IMPORTS.json.xz').read_bytes()));bad=[n for n,v in pins.items() if sha(C/n)!=v['sha256']]
assert not bad,bad
binary={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in [B/'PCF_native/PCF_AuditDriver',B/'PCF_native/PCF_AuditDriver.c',B/'PCF_native/PCF_WALKER.c',B/'PCF_native/PCF_MemoryLimit.c']}
(B/'PCF_AUDIT_BINARY_PINS.json').write_text(json.dumps(binary,indent=1)+'\n')
(B/'PCF_RAW_MANIFEST.json').write_text(json.dumps(dict(files=manifest,all_import_pins_unchanged=True,import_files=len(pins),binary=binary),indent=1)+'\n')
print(json.dumps(dict(raw_text_files=len(manifest),compressed_bytes=sum(x['compressed_bytes'] for x in manifest),all_import_pins_unchanged=True,import_files=len(pins))))

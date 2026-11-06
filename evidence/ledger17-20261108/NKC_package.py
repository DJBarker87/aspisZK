from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent;compressed=[]
for p in E.rglob('*'):
 if not p.is_file():continue
 if p.stat().st_size>20_000_000:
  b=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');compressed.append(str(p.relative_to(E)));p.unlink()
assert not any(p.is_file()and p.stat().st_size>20_000_000 for p in E.rglob('*'))
assert not any(p.is_file()and p.suffix in ['.olean','.ir','.elf','.o']for p in E.rglob('*'))
(E/'NKC_PACKAGING.json').write_text(json.dumps(dict(status='PASS',newly_compressed=compressed,no_file_over20MB=True,no_compiled_objects_or_ELFs=True),indent=1)+'\n')
print(json.dumps(dict(packaging='PASS',newly_compressed=len(compressed))))

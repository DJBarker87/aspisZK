from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent;packed=[]
# Snapshot list prevents iterating over newly created archives.
for p in list(E.rglob('*')):
 if not p.is_file()or p.suffix in['.xz','.sha256']:continue
 if p.stat().st_size>20_000_000:
  b=p.read_bytes();q=Path(str(p)+'.xz');q.write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');packed.append(dict(path=str(p.relative_to(E)),bytes=len(b)));p.unlink()
assert not any(p.is_file()and p.stat().st_size>20_000_000 for p in E.rglob('*'))
assert not any(p.is_file()and p.suffix in['.olean','.ir','.so','.a','.o','.elf','.tar']for p in E.rglob('*'))
(E/'NJW_PACKAGING.json').write_text(json.dumps(dict(status='PASS',newly_packed=packed,files_over20MB=[],binary_objects_committed=False),indent=1)+'\n')
print(json.dumps(dict(stage='packaging',compressed=len(packed),oversize=0)))

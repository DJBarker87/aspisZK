from pathlib import Path
import lzma,hashlib,json
E=Path(__file__).resolve().parent;changed=[]
for p in E.rglob('*'):
 if p.is_file()and p.stat().st_size>20_000_000:
  assert p.suffix!='.xz',str(p)
  b=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');p.unlink();changed.append(str(p.relative_to(E)))
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
print(json.dumps(dict(compressed=changed)))

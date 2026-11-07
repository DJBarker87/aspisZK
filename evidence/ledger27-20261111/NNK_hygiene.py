from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();compressed=json.loads((E/'NNK_HYGIENE.json').read_text()).get('compressed',[])if(E/'NNK_HYGIENE.json').exists()else[]
for p in sorted(E.rglob('*')):
 if not p.is_file()or p.stat().st_size<=20_000_000:continue
 b=p.read_bytes();q=Path(str(p)+'.xz');h=Path(str(p)+'.sha256');z=lzma.compress(b,preset=6);assert lzma.decompress(z)==b;q.write_bytes(z);h.write_text(H(b)+'\n');p.unlink();compressed.append(dict(path=str(p),original_bytes=len(b),sha256=H(b),compressed_bytes=len(z)))
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*')if p.is_file())
assert not any(p.suffix in ['.olean','.ir','.elf']for p in E.rglob('*')if p.is_file())
(E/'NNK_HYGIENE.json').write_text(json.dumps(dict(status='PASS',limit_bytes=20_000_000,compressed=compressed,scope='Only owned evidence; lossless compression before commits; no host cache or keys deleted'),indent=1)+'\n')
print(json.dumps(dict(compressed=len(compressed),large_remaining=0)))

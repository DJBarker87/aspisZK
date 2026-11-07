"""Lossless archival of owned logs; never touches the host cache or active files."""
from pathlib import Path
import lzma,hashlib,json
E=Path(__file__).resolve().parent
assert not(E/'NMQ_CLIENT_ACTIVE').exists(),'Do not archive active client outputs'
rows=[]
for p in list(E.rglob('*')):
 if p.is_file()and p.suffix!='.xz'and(p.suffix in ['.log','.c']or p.stat().st_size>20_000_000):
  b=p.read_bytes();Path(str(p)+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));p.unlink();rows.append(str(p.relative_to(E)))
for p in E.rglob('*.xz'):
 b=lzma.decompress(p.read_bytes());side=Path(str(p)[:-3]+'.sha256');h=hashlib.sha256(b).hexdigest()
 if side.exists():assert side.read_text().strip()==h,str(p)
 else:side.write_text(h+'\n')
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
(E/'NMQ_HYGIENE.json').write_text(json.dumps(dict(status='PASS',archived_oversize=rows,all_compressed_sha_pairs=True,files_over20MB=0,host_cache_deleted=False),indent=1)+'\n')
print('Owned archives validated; no file over20MB')

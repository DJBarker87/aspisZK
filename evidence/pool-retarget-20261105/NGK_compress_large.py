"""Lossless rule-12 archival before every commit; raw SHA256 retained."""
from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent;rows=[]
for p in E.rglob('*'):
 if not p.is_file() or p.stat().st_size<=20000000:continue
 raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();q=Path(str(p)+'.xz');q.write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(h+'\n');assert hashlib.sha256(lzma.decompress(q.read_bytes())).hexdigest()==h
 rows.append(dict(path=str(p.relative_to(E)),raw_bytes=len(raw),sha256=h,compressed_bytes=q.stat().st_size));p.unlink()
manifest=E/'NGK_LARGE_ARCHIVE.json';prior=json.loads(manifest.read_text()) if manifest.exists() else [];manifest.write_text(json.dumps(prior+rows,indent=1)+'\n');print(rows)

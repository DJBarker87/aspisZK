"""Restore committed lossless transports/input references for local reproduction."""
from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent
for p in E.rglob('*.xz'):
 out=Path(str(p)[:-3]);side=Path(str(out)+'.sha256')
 if not side.exists():continue
 b=lzma.decompress(p.read_bytes());assert hashlib.sha256(b).hexdigest()==side.read_text().strip()
 if out.exists():assert out.read_bytes()==b
 else:out.write_bytes(b)
for p in E.rglob('*.reference.json'):
 r=json.loads(p.read_text());b=(E/r['canonical']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'];out=E/r['original_archive']
 if out.exists():assert out.read_bytes()==b
 else:out.write_bytes(b)
print('NJV evidence transports and input references materialized with SHA256 checks')

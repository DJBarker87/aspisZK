from pathlib import Path
import json,hashlib
B=Path.cwd();x=json.loads((B/'NIN_EXPORT.json').read_text());rows=[]
for r in x['files']:
 p=Path(r['path']);assert p.is_file()and p.stat().st_size==r['bytes']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],p
 rows.append(r)
seed=json.loads(__import__('lzma').decompress((B/'NIN_CACHE_IMPORTS.json.xz').read_bytes()))
for r in seed['selected']:
 p=Path(r['destination']);assert p.is_file()and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
out=dict(status='VERIFIED_BEFORE_CLEANUP',export_files=len(rows),export_bytes=sum(r['bytes']for r in rows),seed_files_verified=len(seed['selected']),cache_retained=x['cache_retained'])
(B/'NIN_RETENTION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))

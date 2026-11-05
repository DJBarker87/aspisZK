"""Verify retained own exports and the selected immutable closure, no rebuild."""
from pathlib import Path
import hashlib,json,lzma
B=Path.cwd();x=json.loads((B/'NIL_EXPORT.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for r in x['own_exports']:assert sha(Path(r['source']))==sha(Path(r['destination']))==r['sha256'],r
raw=lzma.decompress((B/'NIL_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==x['closure_sha256']
m=json.loads(raw)
for r in m['files']:assert sha(Path(r['path']))==r['sha256'],r
out=dict(status='PASS',own_exports=len(x['own_exports']),closure_files=len(m['files']),closure_modules=m['modules'],source_to_retained_export='byte-identical',closure_sha256=x['closure_sha256'])
(B/'NIL_CACHE_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

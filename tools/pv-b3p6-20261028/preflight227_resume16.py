"""Read-only source/hash preflight for the exact current generated modules."""
from pathlib import Path
import json,hashlib,re
D=Path('evidence/pv-b3p6-20261028/resume16');sha=lambda x:hashlib.sha256(x).hexdigest()
for r in json.loads((D/'verbatim-prefixes.json').read_text()):
 p=Path(r['path']).read_bytes();src=Path(r['prefix_source']).read_bytes();assert p[:r['prefix_bytes']]==src and sha(src)==r['prefix_sha256'] and sha(p)==r['module_sha256'],r
for q in Path('tools/pv-b3p6-20261028').glob('v244-*/Cargo.toml'):
 if q.parent.name.endswith('16'):assert 'opt-level=3'in q.read_text()
print('all current deployed/reference prefixes checked verbatim')

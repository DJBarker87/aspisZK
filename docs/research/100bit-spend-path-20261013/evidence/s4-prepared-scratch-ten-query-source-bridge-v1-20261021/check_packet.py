#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=root/m['source']['path']
assert sha(s)==m['source']['sha256']
assert m['receipt']['exit_status']==0
assert m['receipt']['source_sha256']==m['source']['sha256']
assert m['receipt']['object_sha256']==m['object']['sha256']
closure=json.loads((root/m['recursive_import_closure']).read_text())
assert len(closure)==m['recursive_import_module_count']==7524
for name,row in closure.items():
 p=Path(row['path'])
 assert p.is_file(),(name,p)
 assert sha(p)==row['sha256'],name
print('PASS: source, receipt, object pin, and all selected import owners')

#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
for mod,spec in m['modules'].items():
 p=root/spec['source']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==spec['source_sha256'], mod
 r=json.loads((root/spec['receipt']).read_text())
 assert r['source_sha256']==spec['source_sha256']
 assert r['exit_status']==0
 for name,owner in m['direct_import_source_map'].items():
  assert Path(owner['source_path']).is_file(), name
  assert hashlib.sha256(Path(owner['source_path']).read_bytes()).hexdigest()==owner['source_sha256'], name
  assert Path(owner['object_path']).is_file(), name
  assert hashlib.sha256(Path(owner['object_path']).read_bytes()).hexdigest()==owner['object_sha256'], name
print('PASS',m['packet'])

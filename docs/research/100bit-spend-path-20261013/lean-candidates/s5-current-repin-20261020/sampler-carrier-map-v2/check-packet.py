#!/usr/bin/env python3
import hashlib,json,pathlib,sys
r=pathlib.Path(__file__).resolve().parent
m=json.loads((r/'manifest.json').read_text())
def sha(p): return hashlib.sha256((r/p).read_bytes()).hexdigest()
for row in m['modules']:
    assert sha(row['source'])==row['source_sha256']
    assert sha(row['receipt'])==row['receipt_sha256']
    rec=json.loads((r/row['receipt']).read_text())
    assert rec['exit_status']==row['exit_status']==0 and rec['object_sha256']==row['object_sha256']
    assert rec['source_sha256']==row['source_sha256']
for name,row in m['direct_import_source_map'].items():
    p=pathlib.Path(row['repository_path'])
    if not p.is_absolute(): p=pathlib.Path.cwd()/p
    assert hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256'], name
    assert row['object_sha256']
print('packet pins verified')

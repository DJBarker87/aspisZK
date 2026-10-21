#!/usr/bin/env python3
import hashlib, json, subprocess, sys
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
def sha(path): return hashlib.sha256((p/path).read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1'
for mod in m['modules']:
    assert sha(mod['source'])==mod['source_sha256']
    rec=json.loads((p/mod['receipt']).read_text())
    assert rec['exit_status']==0 and rec['source_sha256_after']==mod['source_sha256']
    assert rec['object_sha256']==mod['object_sha256']
for name,dep in m['direct_import_source_map'].items():
    assert sha(dep['source'])==dep['source_sha256'],name
    rec=json.loads((p/dep['producer_receipt']).read_text())
    assert rec['exit_status']==0 and rec['source_sha256_after']==dep['source_sha256']
    assert rec['object_sha256']==dep['object_sha256']
expected={f['path'] for f in m['files']}
actual={q.relative_to(p).as_posix() for q in p.rglob('*') if q.is_file() and q.name not in {'manifest.json','SHA256SUMS'}}
assert expected==actual,(actual-expected,expected-actual)
for f in m['files']:
    q=p/f['path']; assert sha(f['path'])==f['sha256'] and q.stat().st_size==f['size_bytes']
assert not list(p.rglob('*.olean')) and not list(p.rglob('*.llbc'))
subprocess.run([sys.executable,str(p/'review/check_loop_body_order.py')],check=True)
assert 'emitted_reader_run_decoded_product_sum' in (p/'evidence/lean.log').read_text()
assert 'propext' in (p/'evidence/lean.log').read_text()
print('PASS:',m['packet'],len(m['files']),'files')

from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
for f in m['files']:
 assert hashlib.sha256((p/f['path']).read_bytes()).hexdigest()==f['sha256'],f['path']
r=json.loads((p/'evidence/receipt.json').read_text())
assert r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None
assert hashlib.sha256((p/'sources/S9SourceResultTransportV1.lean').read_bytes()).hexdigest()==r['source_sha256']
l=(p/'evidence/lean.log').read_text()
assert 'sorryAx' not in l and 'error:' not in l
assert l.count('does not depend on any axioms')==2
assert not any(x.suffix in ('.olean','.llbc','.so','.dylib') for x in p.rglob('*'))
print('PASS: two axiom-free generic transport lemmas and pinned zero-swap check')

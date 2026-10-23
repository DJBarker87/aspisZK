import json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for t in m['targets']: assert t['exit_status']==0 and t['process_swaps']==0 and t['object_sha256']
for f in m['files']:
 p=r/f['path']; assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256']; assert p.stat().st_size==f['bytes']
for p in r.rglob('*'):
 if p.is_file(): assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
l=(r/'proof/lean.log').read_text(); assert 'sorryAx' not in l and 'error:' not in l
assert 'propext' in l and 'Classical.choice' in l and 'Quot.sound' in l
for n in ['v3','v5']:
 d=r/'proof/failed-attempts'/n; assert (d/'receipt.json').exists() and (d/'lean.log').exists()
print('PASS: source-only focused proof packet')

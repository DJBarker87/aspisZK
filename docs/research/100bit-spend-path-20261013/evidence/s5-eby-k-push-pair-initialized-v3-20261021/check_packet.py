#!/usr/bin/env python3
import hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
m = json.loads((ROOT / 'manifest.json').read_text())
r = json.loads((ROOT / 'evidence/receipt.json').read_text())
src = ROOT / 'sources/EbyKPushPairInitializedV1.lean'
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert r['exit_status'] == 0
assert '0  swaps' in (ROOT / 'evidence/lean.log').read_text()
assert hashlib.sha256(src.read_bytes()).hexdigest() == m['modules'][0]['source_sha256'] == r['source_sha256']
assert r['source_sha256'] == r['source_sha256_after']
assert m['modules'][0]['object_sha256'] == r['object_sha256']
assert m['modules'][0]['source_revision'] == r['git_head_at_launch']
log = (ROOT / 'evidence/lean.log').read_text()
for name in ['installed_new_zero', 'first_push_from_new']:
    assert f"'AspisR1S5EbyKPushPairInitializedV1.{name}' depends on axioms:" in log
assert 'sorryAx' not in log
for path in ROOT.rglob('*.olean'):
    raise AssertionError(f'compiled object must not be packaged: {path}')
for owner in m['direct_import_source_map'].values():
    p = ROOT / owner['source']
    assert hashlib.sha256(p.read_bytes()).hexdigest() == owner['source_sha256']
print('packet checks passed')

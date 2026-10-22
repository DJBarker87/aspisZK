#!/usr/bin/env python3
import hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
r = json.loads((ROOT / 'evidence/receipt.json').read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert r['exit_status'] == 0 and r['peak_rss_bytes'] is None and r['swap_bytes'] is None
assert r['source_revision'] is None
assert sha(ROOT / r['source']['path']) == r['source']['sha256']
assert sha(r['object']['path']) == r['object']['sha256']
assert sha(r['compiler']['path']) == r['compiler']['sha256']
for name, pin in r['direct_import_source_map'].items():
    assert sha(pin['repository_source']) == pin['source_sha256'], name
    assert sha(pin['object_path']) == pin['object_sha256'], name
assert sha(r['transitive_actual_parser_source']['source']) == r['transitive_actual_parser_source']['source_sha256']
assert sha(r['transitive_actual_parser_source']['object_path']) == r['transitive_actual_parser_source']['object_sha256']
log = (ROOT / 'evidence/lean.log').read_text()
for theorem, axioms in r['axioms'].items():
    assert theorem in log
    assert all(ax in log for ax in axioms)
    assert 'sorryAx' not in log
assert 'installed_parser_fixed16_strict' in (ROOT / 'sources/S4InstalledCurrentQmParserSourceV1.lean').read_text()
print('PASS: source/object/compiler/import pins and standard axiom report verified; missing telemetry remains explicitly unknown')

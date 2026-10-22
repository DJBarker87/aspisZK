#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent
manifest = json.loads((root / 'manifest.json').read_text())
assert manifest.get('schema') == 'focused-extractor-proof-packet-v1'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
source = root / manifest['source']['path']
assert sha(source) == manifest['source']['sha256']
receipt = json.loads((root / 'evidence/receipt.json').read_text())
assert receipt['exit_code'] == 0
assert receipt['source_sha256'] == manifest['source']['sha256']
assert receipt['object_sha256'] == manifest['object_external_pin']['sha256']
assert manifest['object_external_pin']['not_included'] is True
closure = json.loads((root / 'evidence/import-closure.json').read_text())
assert closure['modules'] == 5125 and closure['missing'] == []
assert closure['owners'] == manifest['selected_import_owners']
for rel, expected in manifest['direct_import_sources'].items():
    assert sha(root / rel) == expected, rel
log = (root / 'evidence/lean.log').read_text()
for declaration in [
 'concrete_qmMul_is_current', 'kpowers_concrete_eq_current',
 'concrete_qmSquare_dispatch', 'concrete_wideAdd_dispatch',
 'concrete_wideMulM31_dispatch', 'concrete_wideMulQM31_dispatch',
 'concrete_wideMul_dispatch', 'concrete_iterFold_law',
 'actualWideMul_total_exact']:
    assert f"AspisR1S9ConcreteFieldOpsV1.{declaration}' depends on axioms:" in log, declaration
assert 'sorryAx' not in log
assert '[propext, Classical.choice, Quot.sound]' in log
for p in root.rglob('*'):
    if p.is_file() and p.suffix in {'.olean', '.ilean', '.c', '.o', '.a'}:
        raise AssertionError(f'compiled artifact included: {p}')
checks = root / 'SHA256SUMS'
for line in checks.read_text().splitlines():
    expected, rel = line.split('  ', 1)
    assert sha(root / rel) == expected, rel
print('S9 focused concrete FieldOps packet PASS')

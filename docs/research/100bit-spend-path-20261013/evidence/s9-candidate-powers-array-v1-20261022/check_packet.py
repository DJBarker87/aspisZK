#!/usr/bin/env python3
import hashlib, json, pathlib, re
root = pathlib.Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((root / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
source = root / manifest['source']
receipt = json.loads((root / manifest['launch_receipt']).read_text())
preflight = json.loads((root / manifest['preflight']).read_text())
command = json.loads((root / manifest['launch_command']).read_text())
log = (root / manifest['lean_raw_log']).read_text()
profile = (root / manifest['profile']).read_text().strip()
assert sha(source) == receipt['source_sha256'] == manifest['source_sha256'] == preflight['source_sha256']
assert receipt == manifest['launch_metrics']
assert receipt['exit_status'] == 0 and receipt['process_swaps'] == 0 and receipt['watchdog_abort'] is None
assert receipt['object_sha256'] == manifest['external_object_sha256']
assert receipt['source_revision_at_launch'] == preflight['source_revision'] == manifest['source_revision_at_launch']
assert 'LEAN_PATH=' + profile in command['argv']
assert '-j1' in command['argv'] and command['argv'][command['argv'].index('-M') + 1] == '4400'
assert sha(root / manifest['profile']) == preflight['profile_sha256']
assert manifest['controller']['sha256'] == receipt['controller_sha256']
assert manifest['controller']['script_retained'] is True
assert sha(root / manifest['controller']['path']) == receipt['controller_sha256']
assert not list(root.rglob('*.olean')) and not list(root.rglob('*.so')) and not list(root.rglob('*.elf'))
for theorem, expected in manifest['theorems'].items():
    reports = re.findall("'" + re.escape(theorem) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
    assert len(reports) == 1
    assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0])) == set(expected)
assert 'sorryAx' not in log and not re.search(r': error(?:\(|:)', log)
assert receipt.get('foreign_lean_samples') == []
for entry in manifest['dependencies']:
    assert preflight['direct_imports'][entry['module']] == entry['object_pin']
checksums = root / 'SHA256SUMS'
for line in checksums.read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(root / rel) == digest, rel
assert 'candidate_explicit_powers4_matches_p6' in source.read_text()
assert 'hmul4' in source.read_text()
print('PASS: S9 focused extractor proof packet; source/receipt/profile pins and standard-axiom theorem verified')

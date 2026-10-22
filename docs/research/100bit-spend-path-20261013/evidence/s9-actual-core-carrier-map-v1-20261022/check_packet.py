#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

root = Path(__file__).resolve().parent
repo = root.parents[4]
research = root.parents[1]
repo = root.parents[4]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((root / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
assert manifest['compiled_objects_included'] is False
assert len(manifest['entries']) == 2
assert manifest['entries'][0]['entry_kind'] == 'compile_only_types'
assert manifest['entries'][0]['theorems'] == {}
assert manifest['entries'][1]['entry_kind'] == 'carrier_map_theorems'

raw_pin = manifest['source_pins']['raw_attempt7_types']
raw_repo_file = repo / raw_pin['raw_attempt7_types_path']
raw_packet_file = root / 'source-pins/RawAttempt7Types.lean'
assert raw_repo_file.is_file() and raw_packet_file.is_file()
assert sha(raw_repo_file) == sha(raw_packet_file) == raw_pin['raw_attempt7_types_sha256']
assert sha(root / raw_pin['clean_owner_source']) == raw_pin['clean_owner_source_sha256']

allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
for entry in manifest['entries']:
    base = root
    source = base / entry['source']
    receipt = json.loads((base / entry['receipt']).read_text())
    preflight = json.loads((base / entry['preflight']).read_text())
    command = json.loads((base / entry['command']).read_text())
    profile = (base / entry['profile']).read_text().strip()
    log = (base / entry['log']).read_text()
    assert source.is_file() and sha(source) == entry['source_sha256'] == receipt['source_sha256']
    assert receipt['exit_status'] == 0 and receipt['process_swaps'] == 0
    assert receipt['watchdog_abort'] is None and receipt['foreign_lean_samples'] == []
    assert receipt['object_sha256'] == entry['object_sha256']
    assert preflight['source_sha256'] == receipt['source_sha256']
    assert preflight['source_revision'] == receipt['source_revision_at_launch']
    assert preflight['no_dependency_builds'] is True
    assert preflight['direct_imports'] == entry['direct_imports']
    assert preflight['controller_sha256'] == receipt['controller_sha256']
    assert 'LEAN_PATH=' + profile in command['argv']
    assert '-j1' in command['argv'] and command['argv'][command['argv'].index('-M') + 1] == '4400'
    assert entry['launch_metrics'] == receipt
    closure = json.loads((base / entry['closure']).read_text())
    assert closure['missing'] == []
    assert closure['modules'] > 0
    for name, pin in entry['direct_imports'].items():
        owner = Path(pin['path'])
        assert owner.is_file() and sha(owner) == pin['sha256'], (name, pin)
    no_comments = re.sub(r'/\-.*?\-/', '', source.read_text(), flags=re.S)
    no_comments = re.sub(r'--[^\n]*', '', no_comments)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', no_comments)
    assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)', no_comments)
    for theorem, axioms in entry['theorems'].items():
        if not axioms:
            assert f"'{theorem}' does not depend on any axioms" in log
        else:
            reports = re.findall("'" + re.escape(theorem) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
            assert len(reports) == 1
            found = set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0]))
            assert found == set(axioms) and found <= allowed_axioms

for ext in ('*.olean', '*.elf', '*.so', '*.dylib', '*.pyc'):
    assert not list(root.rglob(ext)), ext
sum_path = root / 'SHA256SUMS'
for line in sum_path.read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(root / rel) == digest, rel
print('PASS: attempt7 carrier declarations, fieldwise maps, source/import pins, compile receipts, axiom reports, no binaries')

#!/usr/bin/env python3
import hashlib, json, pathlib, sys
packet = pathlib.Path(__file__).resolve().parent
repo = packet.parents[4]
manifest = json.loads((packet / 'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
assert len(manifest['modules']) == 1
mod = manifest['modules'][0]
assert mod['exit_status'] == 0 and mod['swap_bytes'] == 0
assert mod['axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
source = packet / mod['source']
assert sha(source) == mod['source_sha256']
launch = json.loads((packet / mod['command']).read_text())
receipt = json.loads((packet / mod['receipt']).read_text())
log = (packet / mod['lean_log']).read_text()
assert launch['source_sha256'] == mod['source_sha256'] == receipt['source_sha256']
assert launch['lean_sha256'] == receipt['compiler_sha256']
assert launch['argv'][1:3] == ['-j1', '-M4400']
assert receipt['exit_status'] == 0 and '\n                   0  swaps\n' in log
assert receipt['object_sha256'] == mod['object_sha256']
assert "depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
for name, pin in manifest['direct_import_source_map'].items():
    actual = repo / 'docs/research/100bit-spend-path-20261013' / pin['source_path']
    assert actual.exists(), (name, actual)
    assert sha(actual) == pin['source_sha256'], name
# Compiled objects are intentionally referenced by hash/path, not packaged.
assert not list(packet.rglob('*.olean'))
assert not list(packet.rglob('*.ilean'))
print('PASS', manifest['packet'])

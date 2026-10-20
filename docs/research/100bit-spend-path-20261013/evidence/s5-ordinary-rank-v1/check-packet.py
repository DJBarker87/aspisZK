#!/usr/bin/env python3
import hashlib, json, re
from pathlib import Path
ROOT = Path(__file__).resolve().parent

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((ROOT / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
for module in manifest['modules']:
    assert sha(ROOT / module['source']) == module['source_sha256']
    receipt = json.loads((ROOT / module['receipt']).read_text())
    assert receipt['exit_status'] == 0
    assert receipt['object_sha256'] == module['object_sha256']
    assert receipt['source_sha256'] == module['source_sha256']
    assert receipt['wall_seconds'] > 0
    assert receipt['scope_swap_peak_bytes'] == 0
    log = (ROOT / 'attempt/proof-evidence/lean.log').read_text()
    assert all(name in log for name in module['theorems'])
    axioms = sorted(set(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b', log)))
    assert axioms == ['Classical.choice', 'Quot.sound', 'propext']
config = json.loads((ROOT / manifest['evidence']['config']).read_text())
stage = config['stages'][0]
assert stage['source_sha256'] == manifest['modules'][0]['source_sha256']
assert stage['object_sha256'] == manifest['modules'][0]['object_sha256']
command = json.loads((ROOT / manifest['evidence']['command']).read_text())['argv']
assert '-M' in command and command[command.index('-M') + 1] == '4400'
assert '-j1' in command
for module, pin in manifest['direct_import_source_map'].items():
    assert stage['direct_imports'][module] == pin['object_sha256']
    assert sha(ROOT / pin['path']) == pin['source_sha256']
    assert pin['producer_packet'] and pin['producer_receipt']
source_text = (ROOT / manifest['modules'][0]['source']).read_text()
assert not re.search(r'set_option\s+(?:maxHeartbeats|maxRecDepth)', source_text)
for f in ROOT.rglob('*'):
    if f.is_file() and f.name not in {'SHA256SUMS'}:
        assert f.suffix not in {'.olean', '.ilean', '.ir', '.llbc'}
print('ordinary rank packet checks passed')

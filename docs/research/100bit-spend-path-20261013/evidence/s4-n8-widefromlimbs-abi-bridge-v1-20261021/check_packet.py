#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root = Path(__file__).resolve().parent
manifest = json.loads((root / 'manifest.json').read_text())
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
for entry in manifest['files']:
    path = root / entry['path']
    assert path.is_file(), entry['path']
    assert path.stat().st_size == entry['size_bytes'], entry['path']
    assert sha(path) == entry['sha256'], entry['path']
for module in manifest['modules']:
    assert sha(root / module['source']) == module['source_sha256'], module['module']
for name, pin in manifest['direct_import_source_map'].items():
    assert sha(root / pin['source']) == pin['source_sha256'], name
assert manifest['modules'][0]['object_sha256'] == '7ceae3c73ed3c98570ccd05396c7db04651858f693ee5ab73118b226f9e36f08'
print('S4 N8 wideFromLimbs packet checks passed')

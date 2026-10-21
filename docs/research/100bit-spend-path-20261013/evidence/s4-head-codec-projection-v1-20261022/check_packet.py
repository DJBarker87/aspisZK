#!/usr/bin/env python3
import hashlib, json
from pathlib import Path

PKT = Path(__file__).resolve().parent
RESEARCH = PKT.parents[1]
manifest = json.loads((PKT / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
assert manifest['packet'] == PKT.name
assert not list(PKT.rglob('*.olean')), 'compiled objects must remain external'
for row in manifest['files']:
    p = PKT / row['path']
    assert p.is_file(), row['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest() == row['sha256'], row['path']
    assert p.stat().st_size == row['size_bytes'], row['path']
for row in manifest['modules']:
    p = PKT / row['source']
    assert hashlib.sha256(p.read_bytes()).hexdigest() == row['source_sha256'], row['module']
    op = Path(row['object_path'])
    assert op.is_file() and hashlib.sha256(op.read_bytes()).hexdigest() == row['object_sha256'], row['module']
for name, pin in manifest['direct_import_source_map'].items():
    source = RESEARCH / pin['source_path']
    assert source.is_file() and hashlib.sha256(source.read_bytes()).hexdigest() == pin['source_sha256'], name
    obj = Path(pin['object_path'])
    assert obj.is_file() and hashlib.sha256(obj.read_bytes()).hexdigest() == pin['object_sha256'], name
checksums = {}
for line in (PKT / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    checksums[name] = digest
actual = {p.relative_to(PKT).as_posix() for p in PKT.rglob('*') if p.is_file() and p.name != 'SHA256SUMS'}
assert set(checksums) == actual
for name, digest in checksums.items():
    assert hashlib.sha256((PKT / name).read_bytes()).hexdigest() == digest, name
print('PASS', len(actual), 'source/evidence files; external import and object pins verified; no compiled objects packaged')

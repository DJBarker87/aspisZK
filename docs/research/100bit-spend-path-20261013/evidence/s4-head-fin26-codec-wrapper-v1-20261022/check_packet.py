#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
PKT=Path(__file__).resolve().parent; RESEARCH=PKT.parents[1]
m=json.loads((PKT/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['packet']==PKT.name
assert not list(PKT.rglob('*.olean'))
for row in m['files']:
 p=PKT/row['path']; assert p.is_file() and p.stat().st_size==row['size_bytes']; assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
for row in m['modules']:
 p=PKT/row['source']; assert hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256']
 obj=Path(row['object_path']); assert obj.is_file() and hashlib.sha256(obj.read_bytes()).hexdigest()==row['object_sha256']
for name,pin in m['direct_import_source_map'].items():
 s=RESEARCH/pin['source_path']; o=Path(pin['object_path']); assert s.is_file() and hashlib.sha256(s.read_bytes()).hexdigest()==pin['source_sha256']; assert o.is_file() and hashlib.sha256(o.read_bytes()).hexdigest()==pin['object_sha256']
lines=(PKT/'SHA256SUMS').read_text().splitlines(); expected={line.split('  ',1)[1]:line.split('  ',1)[0] for line in lines}; actual={p.relative_to(PKT).as_posix() for p in PKT.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}; assert expected.keys()==actual
for n,h in expected.items(): assert hashlib.sha256((PKT/n).read_bytes()).hexdigest()==h
print('PASS',len(actual),'files; source/object pins verified; no compiled object packaged')

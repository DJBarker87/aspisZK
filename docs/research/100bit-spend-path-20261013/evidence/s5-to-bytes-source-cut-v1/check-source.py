#!/usr/bin/env python3
"""Check the to_le_bytes source-cut pins without requiring a fixed checkout path."""
from pathlib import Path
import hashlib, json, re, sys

here = Path(__file__).resolve().parent
repo = here
while repo != repo.parent and not (repo / 'crates/aspis-core/src/field/wide_exact.rs').is_file():
    repo = repo.parent
if not (repo / 'crates/aspis-core/src/field/wide_exact.rs').is_file():
    raise SystemExit('cannot locate repository source tree')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

pins = json.loads((here / 'source-pins.json').read_text())
source_field = repo / pins['source_files']['source_field_rs']['path']
source_wide = repo / pins['method_span']['path']
bundled = {
    'cut_field_rs': here/'input/field.rs',
    'cut_wide_exact_rs': here/'input/wide_exact.rs',
    'entry_lib_rs': here/'input/lib.rs',
    'cargo_toml': here/'input/Cargo.toml',
    'cargo_lock': here/'input/Cargo.lock',
}
for key, p in [('source_field_rs',source_field),('source_wide_exact_rs',source_wide),*bundled.items()]:
    if not p.is_file() or sha(p) != pins['source_files'][key]['sha256']:
        raise SystemExit(f'hash mismatch or missing file: {key}: {p}')

text = source_wide.read_text()
m = re.search(r'(?m)^    pub fn to_le_bytes\(self\) -> \[u8; Self::BYTE_LEN\] \{.*?^    \}', text, re.S)
if not m: raise SystemExit('method span not found')
span = m.group(0)
if hashlib.sha256(span.encode()).hexdigest() != pins['method_span']['sha256']:
    raise SystemExit('method span hash mismatch')
cut = (here / 'input/wide_exact.rs').read_text()
mc = re.search(r'(?m)^    pub fn to_le_bytes\(self\) -> \[u8; Self::BYTE_LEN\] \{.*?^    \}', cut, re.S)
if not mc or mc.group(0) != span:
    raise SystemExit('copied serializer body differs from current source')
entry = (here / 'input/lib.rs').read_text()
if entry != '#![no_std]\npub mod field;\n\n/// A typed extraction root that calls the source method without altering it.\npub fn wide_exact_to_le_bytes_entry(x: field::WideExact) -> [u8; 32] {\n    x.to_le_bytes()\n}\n':
    raise SystemExit('entry wrapper differs from the pinned mechanical wrapper')
print('PASS: source files, serializer span, and typed entry wrapper match pins')

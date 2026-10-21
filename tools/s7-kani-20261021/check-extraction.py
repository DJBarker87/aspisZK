#!/usr/bin/env python3
"""Check retained emitted bytes, the checked scalar slice, and opaque inventory."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s7-kani-20261021/extraction';P=json.loads((E/'artifact-pins.json').read_text())
for path,pin in P.items():
 p=E/path
 if 'Template' not in path:assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256'],path
f=(E/'generated/S7OwnedP6/Funs.lean').read_text();scalar=(B/'lean/S7OwnedP6ScalarExtracted.lean').read_text()
a=f.index('def residue_scalar_owned\n');b=f.index('/-- [s7_owned_correspondence::residue_owned]',a)
assert f[a:b] in scalar
q=(B/'lean/S7OwnedP6QueryRead.lean').read_text()
a=f.index('def QueryGeometry.for_query\n');b=f.index('/-- [s7_owned_correspondence::weights::QUARTER]',a)
assert f[a:b] in q
for name in ['accumulate_owned','accumulate_optional_owned','query_owned','query_loop_owned','geometry_owned']:
 assert '\ndef '+name+'\n' in f,name
assert not any(x in scalar for x in ['axiom ','sorry','admit','native_decide','set_option max'])
print('All five reference roots emitted; retained bytes and checked scalar slice match')

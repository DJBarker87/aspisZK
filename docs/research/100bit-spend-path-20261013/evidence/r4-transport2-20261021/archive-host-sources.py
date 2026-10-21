#!/usr/bin/env python3
"""Recover the small historical generated crates and check every recorded SHA.
Snapshots are text only. No verifier or failed harness is rerun.
"""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
O=E/'host-sources';O.mkdir(exist_ok=True)
old=(E/'steps-final.rs.txt').read_text()
latest=(E/'steps-final-v2.rs.txt').read_text()
initial=old[:old.index(' #[kani::proof]\n #[kani::unwind(10)]\n fn wide_iterator_order()')]+old[old.index(' // Every array write'):]
pass_only=latest[:latest.index(' fn division_position<const N:usize>()')]+latest[latest.index(' // Every array write'):]
positions=latest[:latest.index(' // Array frame/alias contract')]+latest[latest.index(' // Every array write'):]
prefix=Path('/tmp/cx-r4-transport2-prefix/src/lib.rs').read_text()
for s in [old,latest,initial,pass_only,positions,prefix]:
 h=hashlib.sha256(s.encode()).hexdigest();(O/(h+'.rs.txt')).write_text(s)
for p in (E/'host-inputs').glob('*-inputs.json'):
 d=json.loads(p.read_text());src=O/(d['source_sha256']+'.rs.txt')
 assert src.exists(),(p,d['source_sha256'])
 assert hashlib.sha256(src.read_bytes()).hexdigest()==d['source_sha256']
print('Every historical host source hash has an exact text snapshot')

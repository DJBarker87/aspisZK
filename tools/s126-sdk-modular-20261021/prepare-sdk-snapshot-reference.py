#!/usr/bin/env python3
"""Isolated pure snapshot fission of owned SDK reference, not production code.
Helpers execute the identical Vec<u8>::clone; no operation is abstracted.
Aeneas full-body equivalence and native-context evidence remain explicit gates.
"""
from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[2];base=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3';O=Path(sys.argv[1]);(O/'src').mkdir(exist_ok=True,parents=True)
raw=(base/'src/lib.rs').read_text();s=raw
for role,account in [('public','public'),('proof','proof')]:
 old=f'let {role}_data=sdk.data_cells[{account}.data_slot].bytes.clone();'
 new=f'let {role}_data={role}_snapshot(&sdk.data_cells[{account}.data_slot].bytes);'
 assert s.count(old)==1,old
 s=s.replace(old,new)
helpers='''
pub fn public_snapshot(bytes:&Vec<u8>)->Vec<u8> {bytes.clone()}
pub fn proof_snapshot(bytes:&Vec<u8>)->Vec<u8> {bytes.clone()}
'''
s=s+helpers
(O/'src/lib.rs').write_text(s)
c=(base/'Cargo.toml').read_text().replace('name="aspis-s126-owned-sdk"','name="aspis-s126-owned-sdk-snapshots"')
assert c!=(base/'Cargo.toml').read_text()
(O/'Cargo.toml').write_text(c)
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',parent_source_sha256=sha(raw),source_sha256=sha(s),changes=['factor the same public/proof Vec clone into two concrete nongeneric helper bodies','retain the entire original owned SDK, borrowed counters, AccountInfo metadata, ordinary statuses and all child call sites'],qualification=__doc__,obligations=['compile source extraction','kernel-check complete old/new owned_stage1 equality after literal type/Ops reuse','use only concrete clone-preserving ghost observers in native context checks; no opaque byte-copy replacement','no production adoption or freeze/release-artifact re-pin implied']),indent=2)+'\n')

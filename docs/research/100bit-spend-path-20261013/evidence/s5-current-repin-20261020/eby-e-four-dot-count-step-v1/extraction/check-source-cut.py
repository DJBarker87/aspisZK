#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
repo=Path(sys.argv[1])
kit=Path(sys.argv[2])
fast=repo/'crates/aspis-r1-cost-probe/src/fast_pairing.rs'
actual=fast.read_text()
start=actual.index('mod canonical {')
end=actual.index('/// Candidate exact accumulator for sums of `WideExact * WideExact`.')
expected=actual[start:end].replace('use aspis_core::field::{CM31, QM31, WideExact as E};','use crate::field::{CM31, QM31, WideExact as E};').replace('aspis_core::field::M31','crate::field::M31')
lib=(kit/'lib.rs').read_text()
cut_start=lib.index('mod canonical {')
cut_end=lib.index('\n}\n\npub fn push_entry')
observed=lib[cut_start:cut_end]
assert observed==expected, 'copied canonical/EbyKDot source span mismatch'
for source,rel in [('crates/aspis-core/src/field.rs','field.rs'),('crates/aspis-core/src/field/wide_exact.rs','field/wide_exact.rs')]:
    assert (repo/source).read_bytes()==(kit/rel).read_bytes(), f'{source} is not source-identical'
assert 'pub fn push_entry(mut state: fast_pairing::EbyKDot' in lib
assert 'state.push(value, scalar)?;' in lib
assert 'pub fn new_entry() -> fast_pairing::EbyKDot' in lib
pins=json.loads((kit/'source-pins.json').read_text())
for name,digest in pins['kit_files'].items(): assert hashlib.sha256((kit/name).read_bytes()).hexdigest()==digest, name
print(json.dumps({'ok':True,'source_span_sha256':hashlib.sha256(expected.encode()).hexdigest(),'adapter':'import path substitution only; new_entry/push_entry wrappers'}))

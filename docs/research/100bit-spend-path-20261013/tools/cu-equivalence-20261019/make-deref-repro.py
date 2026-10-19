#!/usr/bin/env python3
"""Freeze a diagnostic projected-reference example; no production source edit."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent
source=b'''pub struct Guard<'a> {
    pub array_mut: &'a mut [u8],
    pub initialized: usize,
}

pub fn projected_len(guard: &mut Guard<'_>) -> usize {
    guard.array_mut.len()
}

pub fn explicit_len(guard: &mut Guard<'_>) -> usize {
    let values: &[u8] = &*guard.array_mut;
    values.len()
}

pub fn direct_len(values: &mut [u8]) -> usize {
    values.len()
}

pub struct Shared<'a> {
    pub array: &'a [u8],
}

pub fn shared_len(guard: &Shared<'_>) -> usize {
    guard.array.len()
}
'''
outputs={'lib.rs':source,
 'Cargo.toml':b'[package]\nname="aspis-cu-deref-repro"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n',
 'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-cu-deref-repro"\nversion = "0.0.0"\n'}
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=dict(scope='Diagnostic only: projected mutable-slice metadata read, explicit shared reborrow, direct mutable slice and projected shared-reference controls. Not a Rust std source admission or replacement.',
    related_library_span='core/src/array/mod.rs:912,954',
    related_compiler_span='charon/src/bin/charon-driver/translate/translate_bodies.rs:970-975',
    toolchain='nightly-2026-06-01',files={n:sha(b) for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    p=here/'deref-repro-input'/name
    if args.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,source_sha256=sha(source),files=len(outputs))))

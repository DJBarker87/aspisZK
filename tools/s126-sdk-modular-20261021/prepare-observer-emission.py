#!/usr/bin/env python3
"""Reproduce literal-None emission independently of the paired caller/linker.
Diagnostic only: no production source or observer assertion is changed.
"""
from pathlib import Path
import sys, json, hashlib
out = Path(sys.argv[1])
(out / 'src').mkdir(parents=True, exist_ok=False)
source = '''#![allow(dead_code,unexpected_cfgs)]
static mut OBSERVED: usize = 0;
#[inline(never)]
fn observer() -> Option<fn()> { None }
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 fn literal_none_after_mutable_zero_write() {
  let value:usize=kani::any();
  unsafe { OBSERVED=value; }
  assert!(observer().is_none(), "literal None is independent of mutable zero static");
  assert_eq!(unsafe { OBSERVED },value);
 }
}
'''
(out / 'src/lib.rs').write_text(source)
(out / 'Cargo.toml').write_text('''[package]
name="aspis-s126-observer-emission"
version="0.0.0"
edition="2021"
[workspace]
[profile.release]
opt-level=3
overflow-checks=true
''')
if len(sys.argv)>2:
 base=Path(sys.argv[2]); original=(base/'src/lib.rs').read_text()
 source=original.rstrip()
 assert source.endswith('}')
 source=source[:-1]+'''
 #[kani::proof]
 fn literal_none_after_mutable_zero_write() {
  let value:usize=kani::any();
  unsafe { OBSERVED=value; }
  assert!(observer().is_none(), "literal None is independent of mutable zero static");
  assert_eq!(unsafe { OBSERVED },value);
 }
}
'''
 (out/'src/lib.rs').write_text(source)
 (out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
(out / 'source-cut.json').write_text(json.dumps(dict(
 schema='focused-extractor-proof-packet-v1', qualification=__doc__,
 source_sha256=hashlib.sha256(source.encode()).hexdigest()), indent=2)+'\n')

#!/usr/bin/env python3
"""Actual CodeField::from_m31 entry, no copied/simplified arithmetic body."""
from pathlib import Path
import sys,json,hashlib
O=Path(sys.argv[1]);assert not O.exists();(O/'src').mkdir(parents=True)
s='''#![no_std]
use aspis_core::{field::{M31,WideExact},r0::CodeField};
pub fn source_from_m31(value:M31)->WideExact {<WideExact as CodeField>::from_m31(value)}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s1-source-m31-embedding-v1"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
aspis-core={path="/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core",default-features=false}
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',entry_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='Extraction/refinement/totality and enclosing query/preparation installation must pass. This entry does not prove whole S1/S6.'),indent=2)+'\n')

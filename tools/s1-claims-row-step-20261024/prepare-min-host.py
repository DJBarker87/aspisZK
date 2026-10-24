#!/usr/bin/env python3
"""One source-context isolation for the initializedness compiler ICE."""
from pathlib import Path
import shutil,json
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');N=H/'s1-claims-row-step-v1-20261024';W=H/'s1-claims-row-step-min-v1-20261024';W.mkdir(exist_ok=False)
for f in ['proofs.rs','run-host.py','admit-host.py','HostAdmission.py','prepare-host.py','Cargo.lock','source-binding.json']:shutil.copyfile(N/f,W/f)
(W/'src').mkdir()
for f in ['r1_wire.rs','sampler.rs','claims_write_proofs.rs']:shutil.copyfile(N/'frozen-probe/src'/f,W/'src'/f)
(W/'src/lib.rs').write_text('''#![no_std]
extern crate alloc;
pub mod sampler;
pub mod r1_wire;
mod r1_semantic {
 use crate::r1_wire::{self as wire,Error};
 use alloc::boxed::Box;
 use aspis_core::field::QM31;
 #[cfg(kani)]
 #[path="../claims_write_proofs.rs"]
 mod claims_write_proofs;
}
''')
# The module path is resolved relative to src/r1_semantic, so keep its directory.
(W/'src/r1_semantic').mkdir()
(W/'Cargo.toml').write_text('''[package]
name="aspis-r1-cost-probe"
version="0.1.0"
edition="2021"
[workspace]
[features]
default=["private-leaf-salts"]
private-leaf-salts=[]
prover=[]
r1p-check=[]
[dependencies]
aspis-core={path="/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core",features=["r0"]}
[profile.release]
opt-level=3
overflow-checks=true
''')
m=json.loads((W/'source-binding.json').read_text());m['context_isolation']='Keep the identical checked fragment, actual adopted r1_wire/ValidatedRecord/Error definitions, sampler module and actual core QM31 dependency; omit unrelated verifier/statement modules and their unused dependency only. This is a fragment gate, not whole-program or SDK/artifact equivalence.';(W/'source-binding.json').write_text(json.dumps(m,indent=2)+'\n')
print(W)

#!/usr/bin/env python3
"""Bounded, direct-source codec comparisons; not a complete leaf inventory."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
assert 'pub const SEMANTIC_BYTES:usize=12903+29*32;' in (R/'crates/aspis-r1-cost-probe/src/verifier.rs').read_text()
for name in ['record_exact_row14']:
 cmd=['timeout','120','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','proofs::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'codec-kani-v4-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation and bounded direct-source codec comparison; arbitrary row-14 32-byte value, retained output on error; not whole-pipeline refinement'),check=True)

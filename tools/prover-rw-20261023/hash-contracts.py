#!/usr/bin/env python3
"""Direct-source parametric digest-call contracts, not hash semantics."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
for name in ['private_leaf_framing','binary_parent_framing']:
 cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','hash_contracts::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'hash-kani-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation, arbitrary oracle answer and leaf bytes, exact call count/slice framing/return; no SHA semantics or privacy conclusion'),check=True)

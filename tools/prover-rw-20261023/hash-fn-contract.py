#!/usr/bin/env python3
"""Check the actual legacy HashFn wrapper and complete private-leaf frame."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','hash_fn_contracts::private_hash_fn_frame','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'hash-fn-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then direct private_leaf_hash/LegacyHashFn delegation, one call with exact slice identity and framing and arbitrary callback answer; no SHA or privacy assertion'),check=True)

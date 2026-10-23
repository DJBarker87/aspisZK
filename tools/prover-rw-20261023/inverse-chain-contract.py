#!/usr/bin/env python3
"""38-call inverse-chain replay, composing already checked CT multiplication."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','inverse_chain_contracts::same_fixed_chain','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'inverse-chain-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation and parametric 38-call replay of pinned fixed inversion chain. Base multiplication is abstracted only after retained CT functional/closure gates; no nonlinear 38-product elimination or unconditional inverse-field-value claim.'),check=True)

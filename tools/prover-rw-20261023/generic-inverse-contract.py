#!/usr/bin/env python3
"""CodeField M31 zero guard/61-call trace against the retained field source."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','generic_inverse_contracts::generic_inverse_guard_and_chain','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'generic-inverse-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation, canonical M31 generic inverse zero guard and fixed 61 multiplication calls over retained CT multiplication contracts; no nonlinear inverse bit-blast'),check=True)

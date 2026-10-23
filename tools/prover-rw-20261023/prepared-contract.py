#!/usr/bin/env python3
"""Check cached multiplier dataflow over the checked lower CT contracts."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','prepared_contracts::cached_multiplier_trace','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'prepared-kani-002',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then cached multiplier constructor/multiply exact ordered calls, operands and result; independent arbitrary canonical lower-kernel answer tapes; no nonlinear multiplication bit-blast'),check=True)

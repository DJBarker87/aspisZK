#!/usr/bin/env python3
"""Selected caller exponent <28, parametric checked QM31 mul/square call traces."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','power_chain_contracts::all_selected_exponents','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'power-chain-kani-003',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation and all 28 concrete public exponents, with symbolic canonical bases/answers, control replay over retained, source-pinned QM31 mul/square kernel contracts; no nonlinear exponent bit-blast or standalone field-power theorem'),check=True)

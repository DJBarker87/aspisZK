#!/usr/bin/env python3
"""Twelve actual CodeField adapter paths over source-pinned scalar contracts."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','scalar_adapter_contracts::arithmetic_forwarding','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'scalar-adapter-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation and twelve arithmetic adapter forwarding paths over already-checked CT scalar kernels; canonical operands/answers, exact operand/call-count/return frames'),check=True)

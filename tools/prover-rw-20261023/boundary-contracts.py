#!/usr/bin/env python3
"""Exact source public-index contracts; not whole coefficient/geometry kernels."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
for name in ['s2_row_and_tags','checked_indices_and_reverse']:
 cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','boundary_contracts::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'boundary-kani-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then exact public S2 row/tag or checked index/reversal/child-parent interface; arbitrary machine-word inputs; no complete coefficient-copy or circle geometry claim'),check=True)

#!/usr/bin/env python3
from pathlib import Path
import subprocess,os
R=Path(__file__).resolve().parents[2]
for name in ['pole_equal_equivalence','pole_fold_equivalence','pole_two_row_equivalence','pole_two_run_scan','pole_compression_equivalence','pole_two_run_compression']:
 cmd=['cargo','kani','--manifest-path','tools/ct-kernels-20261022/Cargo.toml','--lib','--exact','--harness','pole_proofs::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/run-host.py'),'v2-kani-'+name,'timeout','90',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then named bounded pole/compression symbolic gate; no checker elimination'),check=True)

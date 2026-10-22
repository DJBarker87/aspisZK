#!/usr/bin/env python3
from pathlib import Path
import subprocess
R=Path(__file__).resolve().parents[2]
# cm_mul already passed its focused preflight; do not rerun it unchanged.
for name in ['qm_mul','qm_square','qm_mul_m31','qm_mul_cm31','wide_mul','wide_square','wide_mul_m31','wide_mul_qm31']:
 cmd=['cargo','kani','--manifest-path','tools/ct-kernels-20261022/Cargo.toml','--lib','--exact','--harness','parametric::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/run-host.py'),'kani-parametric-v3-'+name,'timeout','90',*cmd],check=True)

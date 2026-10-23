#!/usr/bin/env python3
"""All raw M31 embeddings and canonical F/K/E representation equality."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
for name in ['raw_base_embeddings','canonical_scalar_equalities']:
 cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','representation_contracts::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'representation-kani-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation and direct-source scalar embedding or canonical representation equality; no arithmetic aggregation'),check=True)

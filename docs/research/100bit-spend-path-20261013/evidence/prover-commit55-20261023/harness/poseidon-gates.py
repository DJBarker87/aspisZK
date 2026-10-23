from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
for name,harness in [('poseidon-external-v2','proofs::external'),('poseidon-internal-v2','proofs::internal'),('poseidon-low-folds-v2','proofs::low_folds')]:
 print(name,flush=True)
 rc=subprocess.run(['python3',str(H/'harness/kani-poseidon.py'),name,harness]).returncode
 if rc:sys.exit(rc)

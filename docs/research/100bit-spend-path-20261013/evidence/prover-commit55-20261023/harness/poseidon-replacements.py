from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
status=0
for name,harness in [('poseidon-external-row-v3','proofs::external_row'),('poseidon-low-folds-v3','proofs::low_folds'),('poseidon-internal-v3','proofs::internal')]:
 print(name,flush=True)
 rc=subprocess.run(['python3',str(H/'harness/kani-poseidon.py'),name,harness]).returncode
 status=max(status,rc)
sys.exit(status)

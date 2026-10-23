from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
status=0
for ty,n in [('m31',4),('qm31',4),('wideexact',4),('m31',9),('qm31',10)]:
 name=f'constructor-{ty}-{n}-v1';print(name,flush=True)
 rc=subprocess.run(['python3',str(H/'harness/kani-constructors.py'),name,f'proofs::{ty}_{n}']).returncode
 status=max(status,rc)
sys.exit(status)

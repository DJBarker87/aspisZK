from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
for ty in ['m','q','e']:
 for h in range(1,8):
  name=f'{ty}-split-{2**h}-v2';harness=f'collections::{ty}_split_{2**h}'
  print(name,flush=True)
  rc=subprocess.run(['python3',str(H/'harness/kani.py'),name,harness]).returncode
  if rc:sys.exit(rc)

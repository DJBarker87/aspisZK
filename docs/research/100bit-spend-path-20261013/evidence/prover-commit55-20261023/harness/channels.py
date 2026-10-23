from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
for ty in ['m','q']:
 for lane in range(4):
  name=f'{ty}-channel-{lane}-v4';print(name,flush=True)
  rc=subprocess.run(['python3',str(H/'harness/kani-caller.py'),name,f'fixed_channels::{ty}_channel_{lane}']).returncode
  if rc:sys.exit(rc)

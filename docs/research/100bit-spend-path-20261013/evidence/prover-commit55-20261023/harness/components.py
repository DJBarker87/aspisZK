from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
for word in range(1,8):
 name=f'e-split-256-word{word}-v3';print(name,flush=True)
 rc=subprocess.run(['python3',str(H/'harness/kani-components.py'),name,f'wide_components::split_256_word{word}']).returncode
 if rc:sys.exit(rc)

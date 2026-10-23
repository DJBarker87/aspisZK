from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
for lane in range(4):
 for word in range(4):
  name=f'q-channel-{lane}-word{word}-v5';print(name,flush=True)
  rc=subprocess.run(['python3',str(H/'harness/kani-caller.py'),name,f'channel_components::q_channel_{lane}_word_{word}']).returncode
  if rc:sys.exit(rc)

from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
for mode in ['default','devnet','pool']:
 status=subprocess.run(['python3',str(H/'batch2b-build-retry.py'),mode,sys.argv[1]]).returncode
 if status:raise SystemExit(status)

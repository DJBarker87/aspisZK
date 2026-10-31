from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
r=subprocess.run(['python3',str(H/'extract.py')]);
if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run(['python3',str(H/'translate.py'),sys.argv[1]]).returncode)

"""Owned orchestration: verify completed seed, then one focused attempt at a time."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for script in ['NGF_fetch_seed.py','NGF_queue.py']:
 r=subprocess.run([sys.executable,str(E/script)])
 if r.returncode:sys.exit(r.returncode)

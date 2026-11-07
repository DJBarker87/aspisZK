"""Serial focused checks; each module has its own admission and capped scope."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
attempt=int(sys.argv[1])
for target in sys.argv[2:]:
 r=subprocess.run([sys.executable,str(E/'PCM_run.py'),f'PCM_L{attempt:03d}',target])
 if r.returncode:sys.exit(r.returncode)
 attempt+=1

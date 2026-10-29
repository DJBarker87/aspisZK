#!/usr/bin/env python3
"""Run the explicitly listed focused modules sequentially; stop on any failure."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for pair in sys.argv[1:]:
 attempt,module=pair.split(':',1)
 r=subprocess.run(['python3',str(E/'NEB_run.py'),attempt,module])
 if r.returncode:raise SystemExit(r.returncode)

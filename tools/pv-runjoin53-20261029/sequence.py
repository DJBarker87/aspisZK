"""Focused sequential targets; stop at first rejected declaration."""
from pathlib import Path
import subprocess,sys
T=Path(__file__).parent
for spec in sys.argv[1:]:
 a,m=spec.split(':',1)
 r=subprocess.run([sys.executable,str(T/'focused.py'),a,m])
 if r.returncode:sys.exit(r.returncode)

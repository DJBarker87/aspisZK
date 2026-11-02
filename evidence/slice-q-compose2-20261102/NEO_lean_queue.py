"""One admitted scope at a time; do not compile dependents after failure."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[('NEO_L016','NEO_QRef.Types'),('NEO_L017','NEO_QRef.Funs'),('NEO_L018','NEO_QRepresentation')]
for a,module in jobs:
 r=subprocess.run([sys.executable,str(E/'NEO_run.py'),a,module])
 if r.returncode:raise SystemExit(r.returncode)

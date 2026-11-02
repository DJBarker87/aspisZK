from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,module in [('NEO_L044','NEO_WindowV2.Types'),('NEO_L045','NEO_WindowV2.Funs'),('NEO_L046','NEO_ComplexReference')]:
 r=subprocess.run([sys.executable,str(E/'NEO_run.py'),a,module])
 if r.returncode:raise SystemExit(r.returncode)

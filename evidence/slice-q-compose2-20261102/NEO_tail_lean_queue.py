from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,module in [('NEO_L050','NEO_TailRef.Types'),('NEO_L051','NEO_TailRef.Funs'),('NEO_L052','NEO_TailReference'),('NEO_L053','NEO_ComplexCells')]:
 r=subprocess.run([sys.executable,str(E/'NEO_run.py'),a,module])
 if r.returncode:raise SystemExit(r.returncode)

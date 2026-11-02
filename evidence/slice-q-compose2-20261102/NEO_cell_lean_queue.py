from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,module in [('NEO_L035','NEO_CellRef.Types'),('NEO_L036','NEO_CellRef.Funs'),('NEO_L037','NEO_CellReference')]:
 r=subprocess.run([sys.executable,str(E/'NEO_run.py'),a,module])
 if r.returncode:raise SystemExit(r.returncode)

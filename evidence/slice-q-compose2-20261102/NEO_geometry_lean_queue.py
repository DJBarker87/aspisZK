from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[('NEO_L025','NEO_GetterReference'),('NEO_L026','NEO_GetterCaller'),('NEO_L027','NEO_GeometryScalarRef.Types'),('NEO_L028','NEO_GeometryScalarRef.Funs'),('NEO_L029','NEO_GeometryGather')]
for a,module in jobs:
 r=subprocess.run([sys.executable,str(E/'NEO_run.py'),a,module])
 if r.returncode:raise SystemExit(r.returncode)

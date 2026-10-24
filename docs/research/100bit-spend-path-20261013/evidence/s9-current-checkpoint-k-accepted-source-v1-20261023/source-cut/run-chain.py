from pathlib import Path
import subprocess,sys
w=Path(__file__).resolve().parent
for phase in ["charon","aeneas"]:
 r=subprocess.run([sys.executable,str(w/("run-stage-"+phase+".py"))])
 if r.returncode:raise SystemExit(r.returncode)

from pathlib import Path
import subprocess,sys
w=Path(__file__).resolve().parent
phase=sys.argv[1]
raise SystemExit(subprocess.call([sys.executable,str(w/"run-host.py"),"--root",str(w),"--phase",phase,"--attempt","unrolled-v1","--root-target","both"]))

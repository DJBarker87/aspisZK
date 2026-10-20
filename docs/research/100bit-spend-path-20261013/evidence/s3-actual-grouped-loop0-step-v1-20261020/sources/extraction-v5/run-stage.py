from pathlib import Path
import subprocess,sys
w=Path(__file__).resolve().parent
raise SystemExit(subprocess.run([sys.executable,str(w/"extract-host.py"),"--root",str(w),"--phase",sys.argv[1],"--attempt","a","--root-target","grouped"]).returncode)

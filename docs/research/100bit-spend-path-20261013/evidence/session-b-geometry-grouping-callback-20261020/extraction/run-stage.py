from pathlib import Path
import subprocess,sys
w=Path(__file__).resolve().parent
raise SystemExit(subprocess.call([sys.executable,str(w/'run-host.py'),'--root',str(w),'--phase',sys.argv[1]]))

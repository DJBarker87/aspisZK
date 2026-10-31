from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,t in [('012','NEF_ObserverRef/Types'),('013','NEF_ObserverRef/Funs'),('014','NEF_ExtractedObserver'),('015','NEF_ExtractedTransport')]:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_L'+a,'lean',t]);assert r.returncode==0

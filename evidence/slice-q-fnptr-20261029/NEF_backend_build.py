from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,t in [('022','NEF_BackendRef/Types'),('023','NEF_BackendRef/Funs'),('024','NEF_EmittedBackend')]:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_L'+a,'lean',t]);assert r.returncode==0

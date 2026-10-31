from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,t in [('027','NEF_TailRef/Types'),('028','NEF_TailRef/Funs'),('029','NEF_ExtractedTail')]:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_L'+a,'lean',t]);assert r.returncode==0

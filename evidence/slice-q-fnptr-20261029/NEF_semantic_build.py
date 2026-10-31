from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,t in [('030','NEF_SemanticRef/Types'),('031','NEF_SemanticRef/Funs'),('032','NEF_SemanticObserver')]:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_L'+a,'lean',t]);assert r.returncode==0

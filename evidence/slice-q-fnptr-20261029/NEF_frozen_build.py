from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,t in [('033','NEF_FrozenInvRef/Types'),('034','NEF_FrozenInvRef/Funs'),('035','NEF_FrozenSpecialisation')]:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_L'+a,'lean',t]);assert r.returncode==0

"""Private unchanged predecessors, one module per admitted scope."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,mod in enumerate(['NEF_FrozenInvRef.Funs','NEF_BackendRef.Types','NEF_BackendRef.Funs','NEF_EmittedBackend','NEF_FrozenSpecialisation'],2):
 a=f'NET_L{n:03}'
 r=subprocess.run([sys.executable,str(E/'NET_run.py'),a,mod])
 if r.returncode:sys.exit(r.returncode)

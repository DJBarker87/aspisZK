import subprocess,sys
from pathlib import Path
E=Path(__file__).resolve().parent
for n,m in enumerate(['NEG_FoldsTypes.Types','NEG_FoldsTypes.FunsExternal','NEG_FoldsTypes.Funs','NEG_FoldAssociation','NET_PrefixClosure','NET_GeometryAllocation'],25):
 subprocess.run([sys.executable,str(E/'NET_run.py'),f'NET_L{n:03}',m],check=True)

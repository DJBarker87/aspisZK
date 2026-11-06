from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(17,'NKJ_Small2'),(18,'NKJ_Small3'),(19,'NKJ_Small4'),(20,'NKJ_NativeStep'),(21,'NKJ_NativeFold')]
for n,target in jobs:
 if len(sys.argv)>1 and n<int(sys.argv[1]):continue
 a=f'NKJ_L{n:03}'
 subprocess.run([sys.executable,str(E/'NKJ_config.py'),a,target],check=True)
 r=subprocess.run([sys.executable,str(E/'NKJ_run.py'),a])
 if r.returncode:sys.exit(r.returncode)

from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for n,mod in [(100,'NLC_CopyFrames'),(101,'NLC_ConstructExt'),(102,'NLC_MapCut')]:
 a=f'NLC_L{n:03}'
 subprocess.run([sys.executable,str(E/'NLC_config.py'),a,mod],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 if r.returncode:sys.exit(r.returncode)

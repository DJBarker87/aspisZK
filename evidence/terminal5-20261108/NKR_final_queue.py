from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n in range(186,211):
 a=f'NKR_L{n:03d}'
 r=subprocess.run([sys.executable,str(E/'NKR_run.py'),a])
 c=subprocess.run([sys.executable,str(E/'NKR_classify.py'),a])
 if c.returncode:sys.exit(c.returncode)

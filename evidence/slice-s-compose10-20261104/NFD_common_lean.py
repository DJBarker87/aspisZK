from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for slot in range(15):
 a=f'NFD_L{20+slot:03}';target=f'NFD_CommonField{slot:02}'
 r=subprocess.run([sys.executable,str(E/'NFD_run.py'),a,target]);assert r.returncode==0,('new proof error',a)

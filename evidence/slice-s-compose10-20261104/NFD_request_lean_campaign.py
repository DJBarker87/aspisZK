from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for slot in range(14):
 a=f'NFD_L{6+slot:03}';target=f'NFD_RequestField{slot:02}'
 r=subprocess.run([sys.executable,str(E/'NFD_run.py'),a,target]);assert r.returncode==0,('stop new local proof error',a)

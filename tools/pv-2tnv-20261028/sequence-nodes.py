from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
for n in range(2,21):
 m=f'PV_2TNV_Node{n:02}'
 r=subprocess.run([sys.executable,str(R/'tools/pv-2tnv-20261028/check.py'),str(60923+n),m,'lean/'+m+'.lean'])
 if r.returncode:sys.exit(r.returncode)

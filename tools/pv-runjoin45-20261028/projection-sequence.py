"""Compile the independent single-field projection modules sequentially."""
from pathlib import Path
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];T=R/'tools/pv-runjoin45-20261028'
layers=json.loads((R/'evidence/pv-runjoin45-20261028/projection-layers.json').read_text())
for a,(label,_,_) in enumerate(layers[1:],61203):
 m='R1Z.PV_RunJoin_Coefficient'+label+'45'
 subprocess.run([sys.executable,str(T/'stage-target.py'),m],check=True)
 subprocess.run([sys.executable,str(T/'compile.py'),str(a),'0',m],check=True)

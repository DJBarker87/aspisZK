from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2];a=int(sys.argv[1]);start=int(sys.argv[2])
for j in range(start,81,3):
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin19-20261027/check.py'),str(a),f'R1Z/PV_RunJoin_ValidatorGroup{j:02}19'],cwd=R)
 if p.returncode:sys.exit(p.returncode)
 a+=1

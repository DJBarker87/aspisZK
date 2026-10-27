from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2];a=int(sys.argv[1])
for j in range(9,81,9):
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin19-20261027/check.py'),str(a),f'R1Z/PV_RunJoin_BankCells{j:02}19'],cwd=R)
 if p.returncode:sys.exit(p.returncode)
 a+=1

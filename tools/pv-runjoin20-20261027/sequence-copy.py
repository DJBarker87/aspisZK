from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
for a,start in enumerate(range(0,81,9),37008):
 r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin20-20261027/check.py'),str(a),f'R1Z/PV_RunJoin_CopyGroup{start:02}20'],cwd=R)
 if r.returncode:sys.exit(r.returncode)

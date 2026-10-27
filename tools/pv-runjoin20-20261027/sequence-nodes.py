from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
for a,h in enumerate([5,9,13,17,21,54,34,38,42,46,50],37045):
 r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin20-20261027/check.py'),str(a),f'R1Z/PV_RunJoin_SourceNodes{h:02}20'],cwd=R)
 if r.returncode:sys.exit(r.returncode)

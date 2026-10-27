from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
for a,h in enumerate([0,1,2,3,25,26,27,28,29,30,31,32],37028):
 r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin20-20261027/check.py'),str(a),f'R1Z/PV_RunJoin_SourceSponge{h:02}20'],cwd=R)
 if r.returncode:sys.exit(r.returncode)

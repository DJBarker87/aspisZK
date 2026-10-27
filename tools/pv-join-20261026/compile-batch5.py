from pathlib import Path
import subprocess,sys,json
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume5'
a=int(sys.argv[1])
for target in sys.argv[2:]:
 p=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-check5.py'),str(a),target],cwd=r)
 if p.returncode==78:raise SystemExit(78)
 a+=1

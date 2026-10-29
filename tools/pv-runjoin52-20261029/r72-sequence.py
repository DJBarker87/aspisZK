from pathlib import Path
import sys,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin52-20261029';T=Path(__file__).parent
start=int(sys.argv[1]);off=int(sys.argv[2])
for a,m in enumerate(json.loads((E/'r72-op-sequence.json').read_text())[off:],start):
 assert a<65597
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),'R1Z.'+m])
 if r.returncode:sys.exit(r.returncode)

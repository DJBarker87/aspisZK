from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for n,t in [(55,'NDE_SumComposition'),(56,'NDE_ReconstructTotal')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)

from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(61,'NDE_ReconstructTotal'),(62,'NDE_PackedReference'),(63,'NDE_PackedScan'),(64,'NDE_PackedOuter'),(65,'NDE_PackedAfterTotal')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)

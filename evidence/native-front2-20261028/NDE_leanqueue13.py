from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(75,'NDE_PackedReference'),(76,'NDE_PackedTotal'),(77,'NDE_SimpleBridge'),(78,'NDE_PackedFrame')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)

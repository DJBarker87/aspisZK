from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(58,'NDE_ReconstructTotal'),(59,'NDE_Reference11/Types'),(60,'NDE_Reference11/Funs')]:
 if t.startswith('NDE_Reference11/'):
  p=E/(t+'.lean');p.parent.mkdir(exist_ok=True);p.write_text((E/'NDE_extracted11'/(t+'.lean')).read_text())
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)

from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(66,'NDE_PackedReference'),(67,'NDE_Map'),(68,'NDE_PackedTotal'),(69,'NDE_Reference12/Types'),(70,'NDE_Reference12/Funs'),(71,'NDE_SimpleBridge'),(72,'NDE_Reference13/Types'),(73,'NDE_Reference13/Funs'),(74,'NDE_TerminalBridge')]:
 if t.startswith(('NDE_Reference12/','NDE_Reference13/')):
  version=t.split('/')[0].replace('NDE_Reference','');p=E/(t+'.lean');p.parent.mkdir(exist_ok=True);p.write_text((E/('NDE_extracted'+version)/(t+'.lean')).read_text())
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)

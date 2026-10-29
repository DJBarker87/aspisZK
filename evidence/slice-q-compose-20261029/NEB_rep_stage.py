from pathlib import Path
import subprocess,shutil
E=Path(__file__).resolve().parent
subprocess.run(['python3',str(E/'NEB_extract_representation_run.py'),'NEB_E004'],check=True)
for n in ['Types','Funs']:
 p=E/'NEB_RepresentationRef'/(n+'.lean');p.parent.mkdir(exist_ok=True);shutil.copyfile(E/'NEB_representation_extracted'/'NEB_RepresentationRef'/(n+'.lean'),p)
subprocess.run(['python3',str(E/'NEB_serial_lean.py'),'NEB_L048:NEB_WideRepresentation','NEB_L049:NEB_RepresentationRef.Types','NEB_L050:NEB_RepresentationRef.Funs'],check=True)

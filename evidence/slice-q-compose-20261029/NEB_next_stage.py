"""Dependent sequential stages; refuses advancement after unexpected outcomes."""
from pathlib import Path
import subprocess,shutil
E=Path(__file__).resolve().parent
assert not (E/'NEB_ACTIVE.json').exists()
def run(*args):subprocess.run(['python3',str(E/args[0]),*args[1:]],check=True)
run('NEB_serial_kani.py','NEB_FINAL_RUNS.json')
run('NEB_extract_additive_run.py','NEB_E003')
for n in ['Types','Funs']:
 p=E/'NEB_AdditiveRef'/(n+'.lean');p.parent.mkdir(exist_ok=True);shutil.copyfile(E/'NEB_additive_extracted'/'NEB_AdditiveRef'/(n+'.lean'),p)
run('NEB_serial_lean.py','NEB_L023:NDH_Reference.Types','NEB_L024:NDH_Reference.Funs','NEB_L025:NDH_Geometry','NEB_L026:NEB_PointCalls','NEB_L027:NEB_PointSuccess','NEB_L028:NEB_AdditiveRef.Types','NEB_L029:NEB_AdditiveRef.Funs')

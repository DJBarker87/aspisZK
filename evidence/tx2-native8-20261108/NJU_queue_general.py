from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
modules=json.loads((E/'NJU_GENERALIZATION.json').read_text())['modules'][1:]
for number,module in enumerate(modules,38):
 p=subprocess.run([sys.executable,str(E/'NJU_run.py'),f'NJU_L{number:03d}','lean',module])
 if p.returncode:raise SystemExit('Generalization stopped; inspect the changed theorem, never resubmit unchanged')

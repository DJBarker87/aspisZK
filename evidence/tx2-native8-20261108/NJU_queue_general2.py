from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
modules=json.loads((E/'NJU_GENERALIZATION.json').read_text())['modules'][6:]
for number,module in enumerate(modules,43):
 p=subprocess.run([sys.executable,str(E/'NJU_run.py'),f'NJU_L{number:03d}','lean',module])
 if p.returncode:raise SystemExit('Generalization stopped; inspect changed source')

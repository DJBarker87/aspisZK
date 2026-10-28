from pathlib import Path
import subprocess,json,shutil
E=Path(__file__).resolve().parent
for v in [9,10]:
 d=E/f'NDE_Reference{v}';d.mkdir(exist_ok=True)
 for p in (E/f'NDE_extracted{v}/NDE_Reference{v}').glob('*.lean'):shutil.copyfile(p,d/p.name)
for group in [[(46,'NDE_Reference9/Types'),(47,'NDE_Reference9/Funs'),(48,'NDE_RowBridge')],[(49,'NDE_Reference10/Types'),(50,'NDE_Reference10/Funs'),(51,'NDE_LinearSteps')]]:
 for n,t in group:
  r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
  if r.returncode:raise SystemExit(r.returncode)
  if json.loads((E/f'NDE_L{n:03}/receipt.json').read_text())['exit_status']:break

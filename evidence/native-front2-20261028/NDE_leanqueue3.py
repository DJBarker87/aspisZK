from pathlib import Path
import subprocess,json,shutil
E=Path(__file__).resolve().parent
for v in [4,5,7,8]:
 d=E/f'NDE_Reference{v}';d.mkdir(exist_ok=True)
 for p in (E/f'NDE_extracted{v}/NDE_Reference{v}').glob('*.lean'):shutil.copyfile(p,d/p.name)
groups=[[(16,'NDE_Reference5/Types'),(17,'NDE_Reference5/Funs'),(18,'NDE_LinkBridge')],[(19,'NDE_Reference4/Types'),(20,'NDE_Reference4/Funs'),(21,'NDE_ClaimBridge')],[(22,'NDE_Reference7/Types'),(23,'NDE_Reference7/Funs'),(24,'NDE_CarryStep')],[(25,'NDE_Reference8/Types'),(26,'NDE_Reference8/Funs'),(27,'NDE_PublicBridge')],[(28,'NDE_ArrayExt')]]
for group in groups:
 for n,t in group:
  r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
  if r.returncode:raise SystemExit(r.returncode)
  if json.loads((E/f'NDE_L{n:03}/receipt.json').read_text())['exit_status']:break

from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for n,t in [(9,'NDE_Reference3/Types'),(10,'NDE_Reference3/Funs'),(11,'NDE_VariantBridge')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode or json.loads((E/f'NDE_L{n:03}/receipt.json').read_text())['exit_status']:break

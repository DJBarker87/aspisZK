from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for n,t in [(4,'NDE_Reference2/Types'),(5,'NDE_Reference2/Funs'),(6,'NDE_RawBridge')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode or json.loads((E/f'NDE_L{n:03}/receipt.json').read_text())['exit_status']:break

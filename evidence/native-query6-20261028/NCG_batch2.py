from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
assert json.loads((E/'NCG_K005/receipt.json').read_text())['exit_status']==1
for n,h in [(6,'horner_one'),(7,'horner_one_negative'),(8,'horner_three'),(9,'horner_three_negative')]:
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)

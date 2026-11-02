"""Serial focused unchanged prerequisites; stop at the first nonzero receipt."""
from pathlib import Path
import subprocess,json,os
E=Path(__file__).resolve().parent
plan=json.loads((E/'NEI_ACCUM_PREREQUISITE_PLAN.json').read_text());assert not plan['absent']
for index,module in enumerate(plan['order'],103):
 attempt=f'NEI_L{index:03d}';assert not (E/(attempt+'-launcher.log')).exists()
 env=dict(os.environ,NEI_UNCHANGED_MODULE='1')
 r=subprocess.run(['python3',str(E/'NEI_run.py'),attempt,'lean',module],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 d=json.loads((E/attempt/'receipt.json').read_text())
 if d['exit_status'] or any('sorryAx' in t for t in d['print_axioms']):raise SystemExit(1)

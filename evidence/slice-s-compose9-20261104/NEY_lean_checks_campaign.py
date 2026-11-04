"""One new field-coordinate check per admitted capped Lean scope."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(5,'NEY_Field00'),(6,'NEY_Field12'),(7,'NEY_BindingSuccess'),(8,'NEY_ResultEncoderOracle')]+[(n,f'NEY_Field{slot:02}') for n,slot in enumerate([s for s in range(26) if s not in [0,12]],9)]
assert len(jobs)==28 and jobs[-1][0]==32
for n,module in jobs:
 a=f'NEY_L{n:03}'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'NEY_run.py'),a,module])
 if r.returncode!=0:raise SystemExit('Focused elaboration/preflight failed: inspect before dependent check')
 print(json.dumps(dict(attempt=a,module=module)),flush=True)

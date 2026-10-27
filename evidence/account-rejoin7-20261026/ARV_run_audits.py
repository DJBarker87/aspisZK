"""Sequential task orchestration over the unchanged per-module host launcher."""
from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent
for row in json.loads((P/'ARV_AUDIT_PLAN.json').read_text()):
    n=row['attempt']; mod=row['module']
    with (P/f'ARV_{n:03}-orchestration.log').open('w') as log:
        result=subprocess.run([sys.executable,str(P/'ARV_compile.py'),str(n),mod],stdout=log,stderr=subprocess.STDOUT)
    print(json.dumps(dict(attempt=n,module=mod,exit=result.returncode)),flush=True)
    if result.returncode:sys.exit(result.returncode)

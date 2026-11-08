"""One unchanged host launcher invocation at a time; stop at any failure."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
order=json.loads((E/'NNM_REV4_ORDER.json').read_text())
for i,m in enumerate(order[1:],3):
 r=subprocess.run([sys.executable,str(E/'NNM_run.py'),f'NNM_L{i:03}','rsl',m])
 if r.returncode:sys.exit(r.returncode)

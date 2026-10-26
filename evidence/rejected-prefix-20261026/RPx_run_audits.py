"""Sequential task invocations of the existing capped launcher, one scope at a time."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for item in json.loads((E/'RPx_audit_plan.json').read_text()):
    n=int(item['attempt'].split('_')[1])
    print(item['attempt'],item['module'],flush=True)
    r=subprocess.run([sys.executable,str(E/'RPx_compile.py'),str(n),item['module']],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(r.stdout[-1600:],flush=True)
    if r.returncode:sys.exit(r.returncode)

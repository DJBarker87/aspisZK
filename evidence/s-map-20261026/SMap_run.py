from pathlib import Path
import json,subprocess,sys
p=Path(__file__).resolve().parent
for x in json.loads((p/'SMap_plan.json').read_text()):
 print(x['attempt'],x['module'],flush=True)
 r=subprocess.run([sys.executable,str(p/'SMap_compile.py'),str(int(x['attempt'].split('_')[1])),x['module']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(r.stdout[-1600:],flush=True)
 if r.returncode:sys.exit(r.returncode)

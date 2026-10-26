from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent
for item in json.loads((P/'Rc7_audit_plan.json').read_text()):
 n=int(item['attempt'].split('_')[1]);print(item['attempt'],item['module'],flush=True)
 result=subprocess.run([sys.executable,str(P/'Rc7_compile.py'),str(n),item['module']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(result.stdout[-1200:],flush=True)
 if result.returncode:sys.exit(result.returncode)

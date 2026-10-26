from pathlib import Path
import subprocess,json
P=Path(__file__).resolve().parent
mods=json.loads((P/'FIs_audit_plan.json').read_text())+json.loads((P/'FIs_extra_plan.json').read_text())
assert len(mods)==55
for n,m in enumerate(mods,45):
 print(n,m,flush=True)
 r=subprocess.run(['python3',str(P/'FIs_compile.py'),str(n),m])
 if r.returncode:break

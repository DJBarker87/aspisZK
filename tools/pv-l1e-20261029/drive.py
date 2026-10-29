"""Sequential one-module attempts, stopping on failure or admission refusal."""
from pathlib import Path
import json,subprocess,sys
E=Path('evidence/pv-l1e-20261029')
a=int(sys.argv[1]);order=sys.argv[2:] or json.loads((E/'missing-order.json').read_text())
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
for m in order:
 if m in accepted:continue
 if a>=66597:break
 r=subprocess.run(['python3','tools/pv-l1e-20261029/compile.py',str(a),'0',m])
 if r.returncode:print('STOP NEXT',a+1,flush=True);sys.exit(r.returncode)
 a+=1
print('NEXT',a,flush=True)

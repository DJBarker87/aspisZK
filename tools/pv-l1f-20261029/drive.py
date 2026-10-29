"""Sequential one-module attempts, stopping on failure or admission refusal."""
from pathlib import Path
import json,subprocess,sys
E=Path('evidence/pv-l1f-20261029')
a=int(sys.argv[1]);order=sys.argv[2:] or json.loads((E/'missing-order.json').read_text())
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
for m in order:
 if m in accepted:continue
 if a>=67197:break
 r=subprocess.run(['python3','tools/pv-l1f-20261029/compile.py',str(a),'0',m])
 if r.returncode:print('STOP RETRY SAME ID AFTER COOLDOWN' if r.returncode in (77,78) else 'STOP NEXT',a if r.returncode in (77,78) else a+1,flush=True);sys.exit(r.returncode)
 a+=1
print('NEXT',a,flush=True)

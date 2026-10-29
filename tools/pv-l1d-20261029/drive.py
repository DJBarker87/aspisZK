"""Sequential focused proof order; stop immediately on a changed target's error."""
from pathlib import Path
import json,subprocess,sys
E=Path('evidence/pv-l1d-20261029')
a=int(sys.argv[1]);order=json.loads((E/'missing-order.json').read_text())+json.loads((E/'priority-order.json').read_text())
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
for m in order:
 if m in accepted:continue
 if a>=65897:break
 r=subprocess.run(['python3','tools/pv-l1d-20261029/compile.py',str(a),'0',m])
 if r.returncode:sys.exit(r.returncode)
 a+=1
print('NEXT',a,flush=True)

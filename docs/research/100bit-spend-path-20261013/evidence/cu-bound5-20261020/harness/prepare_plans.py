"""Pin bound4's measured byte corpus; rerun each input on the candidate."""
import json,sys
from pathlib import Path
H=Path(sys.argv[1]);O=H.parent/'codex-cx-cu-bound4-20261020'
for name in ['control','variants','variants-extra','targeted','random-a','random-b']:
 p=json.loads((O/f'plan-{name}.json').read_text())
 for k in ['driver','pool','verifier','out']:p[k]=p[k].replace(str(O),str(H))
 # Controls use the task's copy; random/grid --reuse continues to pin the
 # original OS-masked proof/public corpus rather than reconstructing a mask.
 if name=='control':
  for r in p['runs']:r['args']=[a.replace(str(O),str(H)) for a in r['args']]
 (H/f'plan-{name}.json').write_text(json.dumps(p,indent=1)+'\n')
print('Six candidate plans prepared with inherited exact proof/public bytes')

#!/usr/bin/env python3
"""Read retained host LLBC; do not rerun extraction or transfer its payload."""
import json,subprocess,sys
from pathlib import Path
E=Path(__file__).resolve().parent.parent
version=int(sys.argv[1]) if len(sys.argv)>1 else 3
assert 1<=version<=3
filename='ProverMaterial13.llbc' if version==1 else f'ProverMaterial13-v{version}.llbc'
outname='material-function-inventory.json' if version==1 else f'material-function-inventory-v{version}.json'
code='''import json
from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit13-20261021/extraction')/%r
x=json.loads(p.read_text());rows=[]
for f in x['translated']['fun_decls']:
 if f is None:continue
 meta=f['item_meta'];name=meta['name'];body=f.get('body')
 rows.append(dict(id=f['def_id'],name=name,has_body=isinstance(body,dict),body_kind=list(body) if isinstance(body,dict) else body,span=meta.get('span')))
print(json.dumps(dict(has_errors=x['has_errors'],functions=rows),indent=2))
'''%filename
(E/outname).write_text(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True))
x=json.loads((E/outname).read_text())
for f in x['functions']:
 name=json.dumps(f['name'])
 if any('"'+n+'"' in name for n in ['m31','qm31','build_mask_material_for_layout','balance_m31_copy_inactive','balance_qm31_copy_inactive']):
  print('body_kind='+str(f['body_kind']),name)

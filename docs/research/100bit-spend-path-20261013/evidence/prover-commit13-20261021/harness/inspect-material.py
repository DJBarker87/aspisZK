#!/usr/bin/env python3
"""Read retained host LLBC; do not rerun extraction or transfer its payload."""
import json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
code='''import json
from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit13-20261021/extraction/ProverMaterial13-v2.llbc')
x=json.loads(p.read_text());rows=[]
for f in x['translated']['fun_decls']:
 if f is None:continue
 meta=f['item_meta'];name=meta['name']
 rows.append(dict(id=f['def_id'],name=name,has_body=isinstance(f.get('body'),dict),body_kind=list(f['body']) if isinstance(f.get('body'),dict) else f.get('body'),span=meta.get('span')))
print(json.dumps(dict(has_errors=x['has_errors'],functions=rows),indent=2))
'''
(E/'material-function-inventory-v2.json').write_text(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True))
x=json.loads((E/'material-function-inventory-v2.json').read_text())
for f in x['functions']:
 name=json.dumps(f['name'])
 if any('"'+n+'"' in name for n in ['m31','qm31','build_mask_material_for_layout','balance_m31_copy_inactive','balance_qm31_copy_inactive']):
  print('body='+str(f['has_body']),name)

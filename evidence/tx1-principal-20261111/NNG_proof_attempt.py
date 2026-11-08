"""Prepare one NNG-owned focused proof input; no launcher changes."""
from pathlib import Path
import json,sys,re
E=Path(__file__).resolve().parent
attempt,module=sys.argv[1:]
assert re.fullmatch(r'NNG_L[0-9]{4}',attempt)
assert re.fullmatch(r'NNG_[A-Za-z0-9_]+',module)
assert not (E/(attempt+'.json')).exists()
s=(E/(module+'.lean')).read_text()
(E/'NNG_generated'/(module+'.lean')).write_text(s)
x=json.loads((E/'NNG_L1002.json').read_text())
for k in ['deps_fingerprint','source_revision','source_tree_dirty']:x.pop(k,None)
x.update(attempt=attempt,module=module,sources=['NNG_generated/'+module+'.lean'])
b='/home/dombarker/project-offloads/codex-cx-tx1-principal-20261111'
roots=x['env']['LEAN_PATH'].split(':')
x['env']['LEAN_PATH']=':'.join([roots[0],b+'/NNG_WrapperR4_objects',b+'/NNG_Wrapper_objects',*roots[1:]])
x['command']=[v.replace('NNG_BindAssociation345',module) for v in x['command']]
(E/(attempt+'.json')).write_text(json.dumps(x,indent=2))

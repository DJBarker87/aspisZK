from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
attempt,module=sys.argv[1:3];b='/home/dombarker/project-offloads/codex-cx-terminal5-20261108'
x=dict(attempt=attempt,kind='lean',module=module,sources=[module+'.lean','NKR_seed.py','NKR_NKI_EXPORT.json','NKR_NKN_EXPORT.json'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.','-o','NKR_objects/'+module+'.olean',module+'.lean'],timeout=180,expected_time='Focused symbolic parent composition',env=dict(LEAN_PATH=':'.join(json.loads((E/'NKR_PATH.json').read_text())),CARGO_TARGET_DIR=b+'/NKR_target'),collect=['NKR_SEED.json'])
(E/(attempt+'.json')).write_text(json.dumps(x))

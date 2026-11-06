from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-circle-points-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,module=sys.argv[1:];src='NKM_generated/'+module.replace('.','/')+'.lean'
p=E/src;p.parent.mkdir(parents=True,exist_ok=True)
if (E/(module+'.lean')).exists():p.write_text((E/(module+'.lean')).read_text())
paths=[B+'/NKM_objects',B+'/NKM_seed/NKH']+json.loads((E.parent/'ledger18-20261108/NKH_PATHS.json').read_text())
x=dict(attempt=a,kind='lean',module=module,sources=[src],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NKM_generated','-o','NKM_objects/'+module.replace('.','/')+'.olean',src],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKM_tmp',CARGO_TARGET_DIR=B+'/NKM_target',LEAN_PATH=':'.join(paths)),collect=[],timeout=180,expected_time='Focused single-module Lean elaboration against retained coherent objects')
(E/(a+'.json')).write_text(json.dumps(x))

from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,mod=sys.argv[1:]
x=dict(attempt=a,kind='lean',module=mod,sources=['NLC_generated/'+mod+'.lean'],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NLC_generated','-o','NLC_objects/'+mod+'.olean','NLC_generated/'+mod+'.lean'],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLC_tmp',CARGO_TARGET_DIR=B+'/NLC_target',LEAN_PATH=':'.join(json.loads((E/'NLC_PATHS.json').read_text()))),timeout=180,expected_time='Focused symbolic source/cut proof; reused coherent objects')
(E/(a+'.json')).write_text(json.dumps(x))

from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-top-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,mod=sys.argv[1:]
x=dict(attempt=a,kind='lean',module=mod,sources=['NLV_generated/'+mod+'.lean'],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NLV_generated','-o','NLV_objects/'+mod+'.olean','NLV_generated/'+mod+'.lean'],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLV_tmp',CARGO_TARGET_DIR=B+'/NLV_target',LEAN_PATH=':'.join(json.loads((E/'NLV_PATHS.json').read_text()))),timeout=180,expected_time='Focused symbolic source/cut proof; reused coherent objects')
(E/(a+'.json')).write_text(json.dumps(x))

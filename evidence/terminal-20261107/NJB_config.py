from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-terminal-20261107';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,mod=sys.argv[1:];paths=[B+'/NJB_objects']+json.loads((E/'NJB_PATHS.json').read_text())
x=dict(attempt=a,kind='lean',module=mod,sources=[mod+'.lean'],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.', '-o','NJB_objects/'+mod+'.olean',mod+'.lean'],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_SYSROOT=T,LEAN_PATH=':'.join(paths),CARGO_TARGET_DIR=B+'/NJB_target',TMPDIR=B+'/NJB_tmp'),deps_fingerprint={},expected_time='Focused single-module elaboration; pinned coherent cohort imports')
(E/(a+'.json')).write_text(json.dumps(x,indent=1)+'\n')

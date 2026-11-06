from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NLC_COMBINED_IMPORT',sources=['NLC_generated/NLC_ProofDriver.lean','NLC_generated/NLC_Driver.lean','NLC_audit_batch.py','NLC_AUDIT_ROOTS.json','NLC_AUDIT_MODULES.json','NLC_EXPECTED_IMPORTS.jsonl'],command=['python3','NLC_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLC_tmp',CARGO_TARGET_DIR=B+'/NLC_target',LEAN_PATH=':'.join(json.loads((E/'NLC_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NLC_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NLC_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NLC_pin.py','NLC_PREDECESSOR_PINS.json.xz'];x['collect']=['NLC_CLOSURE_PINS.json.xz','NLC_CLOSURE_PINS.json.sha256','NLC_TOOL_PINS.json','NLC_PREDECESSOR_COMPARISON.json','NLC_EXPORT.json']
(E/(a+'.json')).write_text(json.dumps(x))

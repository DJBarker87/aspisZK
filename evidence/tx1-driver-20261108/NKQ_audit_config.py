from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NKQ_COMBINED_IMPORT',sources=['NKQ_generated/NKQ_ProofDriver.lean','NKQ_generated/NKQ_Driver.lean','NKQ_audit_batch.py','NKQ_AUDIT_ROOTS.json','NKQ_AUDIT_MODULES.json','NKQ_EXPECTED_IMPORTS.jsonl'],command=['python3','NKQ_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKQ_tmp',CARGO_TARGET_DIR=B+'/NKQ_target',LEAN_PATH=':'.join(json.loads((E/'NKQ_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NKQ_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NKQ_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NKQ_pin.py','NKQ_PREDECESSOR_PINS.json.xz'];x['collect']=['NKQ_CLOSURE_PINS.json.xz','NKQ_CLOSURE_PINS.json.sha256','NKQ_TOOL_PINS.json','NKQ_PREDECESSOR_COMPARISON.json','NKQ_EXPORT.json']
(E/(a+'.json')).write_text(json.dumps(x))

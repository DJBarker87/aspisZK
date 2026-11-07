from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-observed-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NLR_COMBINED_IMPORT',sources=['NLR_generated/NLR_ProofDriver.lean','NLR_generated/NLR_Driver.lean','NLR_audit_batch.py','NLR_AUDIT_ROOTS.json','NLR_AUDIT_MODULES.json','NLR_EXPECTED_IMPORTS.jsonl'],command=['python3','NLR_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLR_tmp',CARGO_TARGET_DIR=B+'/NLR_target',LEAN_PATH=':'.join(json.loads((E/'NLR_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NLR_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NLR_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NLR_pin.py','NLR_PREDECESSORS.json.xz'];x['collect']=['NLR_CLOSURE_PINS.json.xz','NLR_CLOSURE_PINS.json.sha256','NLR_TOOL_PINS.json','NLR_PREDECESSOR_COMPARISON.json','NLR_EXPORT.json']
(E/(a+'.json')).write_text(json.dumps(x))

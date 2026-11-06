from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-prepare-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NLJ_COMBINED_IMPORT',sources=['NLJ_generated/NLJ_ProofDriver.lean','NLJ_generated/NLJ_Driver.lean','NLJ_audit_batch.py','NLJ_AUDIT_ROOTS.json','NLJ_AUDIT_MODULES.json','NLJ_EXPECTED_IMPORTS.jsonl'],command=['python3','NLJ_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLJ_tmp',CARGO_TARGET_DIR=B+'/NLJ_target',LEAN_PATH=':'.join(json.loads((E/'NLJ_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NLJ_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NLJ_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NLJ_pin.py','NLJ_PREDECESSORS.json.xz'];x['collect']=['NLJ_CLOSURE_PINS.json.xz','NLJ_CLOSURE_PINS.json.sha256','NLJ_TOOL_PINS.json','NLJ_PREDECESSOR_COMPARISON.json','NLJ_EXPORT.json']
(E/(a+'.json')).write_text(json.dumps(x))

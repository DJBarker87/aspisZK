from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-finish2-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NLU_COMBINED_IMPORT',sources=['NLU_generated/NLU_ProofDriver.lean','NLU_generated/NLU_Driver.lean','NLU_audit_batch.py','NLU_AUDIT_ROOTS.json','NLU_AUDIT_MODULES.json','NLU_EXPECTED_IMPORTS.jsonl'],command=['python3','NLU_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLU_tmp',CARGO_TARGET_DIR=B+'/NLU_target',LEAN_PATH=':'.join(json.loads((E/'NLU_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NLU_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NLU_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NLU_pin.py','NLU_PREDECESSORS.json.xz','NLU_preflight.py'];x['collect']=['NLU_CLOSURE_PINS.json.xz','NLU_CLOSURE_PINS.json.sha256','NLU_TOOL_PINS.json','NLU_PREDECESSOR_COMPARISON.json','NLU_EXPORT.json','NLU_PREFLIGHT.json']
(E/(a+'.json')).write_text(json.dumps(x))

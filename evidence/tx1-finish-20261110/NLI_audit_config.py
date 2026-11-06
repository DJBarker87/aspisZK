from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-finish-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NLI_COMBINED_IMPORT',sources=['NLI_generated/NLI_ProofDriver.lean','NLI_generated/NLI_Driver.lean','NLI_audit_batch.py','NLI_AUDIT_ROOTS.json','NLI_AUDIT_MODULES.json','NLI_EXPECTED_IMPORTS.jsonl'],command=['python3','NLI_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLI_tmp',CARGO_TARGET_DIR=B+'/NLI_target',LEAN_PATH=':'.join(json.loads((E/'NLI_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NLI_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NLI_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NLI_pin.py','NLI_PREDECESSORS.json.xz'];x['collect']=['NLI_CLOSURE_PINS.json.xz','NLI_CLOSURE_PINS.json.sha256','NLI_TOOL_PINS.json','NLI_PREDECESSOR_COMPARISON.json','NLI_EXPORT.json']
(E/(a+'.json')).write_text(json.dumps(x))

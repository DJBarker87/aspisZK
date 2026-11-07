from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-top-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NLV_COMBINED_IMPORT',sources=['NLV_generated/NLV_ProofDriver.lean','NLV_generated/NLV_Driver.lean','NLV_audit_batch.py','NLV_AUDIT_ROOTS.json','NLV_AUDIT_MODULES.json','NLV_EXPECTED_IMPORTS.jsonl'],command=['python3','NLV_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLV_tmp',CARGO_TARGET_DIR=B+'/NLV_target',LEAN_PATH=':'.join(json.loads((E/'NLV_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NLV_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NLV_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NLV_pin.py','NLV_PREDECESSORS.json.xz'];x['collect']=['NLV_CLOSURE_PINS.json.xz','NLV_CLOSURE_PINS.json.sha256','NLV_TOOL_PINS.json','NLV_PREDECESSOR_COMPARISON.json','NLV_EXPORT.json']
(E/(a+'.json')).write_text(json.dumps(x))

from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];B='/home/dombarker/project-offloads/codex-cx-tx1-finish3-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
x=dict(attempt=a,kind='audit',module='NMC_COMBINED_IMPORT',sources=['NMC_generated/NMC_ProofDriver.lean','NMC_generated/NMC_Driver.lean','NMC_audit_batch.py','NMC_AUDIT_ROOTS.json','NMC_AUDIT_MODULES.json','NMC_EXPECTED_IMPORTS.jsonl'],command=['python3','NMC_audit_batch.py',mode],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NMC_tmp',CARGO_TARGET_DIR=B+'/NMC_target',LEAN_PATH=':'.join(json.loads((E/'NMC_PATHS.json').read_text()))),timeout=180,expected_time='One raw ax2 group or NFX loaded scan; unchanged walker, fully pinned combined closure',collect_globs=['NMC_audit/'+mode+'/*'])
if mode=='scan':x['collect']=['NMC_LOADED_scan.jsonl']
if mode=='close':
 x['sources']+=['NMC_pin.py','NMC_PREDECESSORS.json.xz','NMC_preflight.py','NMC_patch_inputs.py','NMC_PATCH_INPUT_PINS.json','NMC_HARNESSES.patch','NMC_HARNESSES.patch.sha256','NMC_PATCH_EXPORT.json','NMC_SOURCE_PINS.json','NMC_BASE_EXPECTED.json','NMC_SEED_PINS.json'];x['collect']=['NMC_CLOSURE_PINS.json.xz','NMC_CLOSURE_PINS.json.sha256','NMC_TOOL_PINS.json','NMC_PREDECESSOR_COMPARISON.json','NMC_EXPORT.json','NMC_PREFLIGHT.json','NMC_SOLVER_CLEANUP.json']
(E/(a+'.json')).write_text(json.dumps(x))

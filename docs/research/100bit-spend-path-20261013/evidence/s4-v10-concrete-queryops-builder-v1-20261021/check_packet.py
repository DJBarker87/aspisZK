#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
src=p/'sources/S4V10ConcreteQueryOpsBuilderV1.lean'
rec=json.loads((p/'receipts/receipt-v3.json').read_text())
pre=json.loads((p/'receipts/preflight-v3.json').read_text())
assert rec['exit_status']==0
assert rec['source_sha256']==sha(src)==pre['source_sha256']
assert rec['object_sha256'] and rec['launch_revision']==pre['launch_revision']
assert rec['wall_seconds']>0 and rec['peak_aggregate_rss_bytes']>0
assert '0  swaps' in (p/'receipts/time-v3.log').read_text()
log=(p/'receipts/lean-v3.log').read_text()
for theorem in ['concrete_candidate_dots_is_literal_v10','concrete_candidate_query_refines_old_model']:
 assert f"AspisR1FastDotsV10ConcreteQueryOpsBuilderV1.{theorem}' depends on axioms" in log
 assert 'sorryAx' not in log
assert 'def concreteCandidateQueryOps (rest : QueryOps)' in src.read_text()
assert 'withLiteralDots concreteOps rest' in src.read_text()
assert 'base : Ops' not in src.read_text()
for name,pin in pre['selected_imports'].items():
 assert Path(pin['path']).is_file(),name
 assert sha(Path(pin['path']))==pin['sha256'],name
binding=json.loads((p/'source-evidence/current-stage2-source-binding.json').read_text())
for key in ['query_advance_object','query_loop_object']:
 pin=binding[key]; artifact=Path(pin['path']); assert artifact.is_file(); assert sha(artifact)==pin['sha256']
assert binding['query_advance_source_sha256']=='9d7eb55883d5f8215d0eddaea737b60ace37c16a4a498d1f2f903110f14fbbfd'
assert binding['query_loop_source_sha256']=='c398ba41273939ac739a064eee492976988027ff1b1d6f33657480b17aed0def'
import subprocess
subprocess.run(['python3', str(p/'source-evidence/check_stage2_source_binding.py')], check=True)
print('PASS: source, receipt, axioms, and direct imported object pins verified')

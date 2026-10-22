#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
W=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (W/'SHA256SUMS').read_text().splitlines():
 expected,rel=line.split('  ',1);p=W/rel
 assert p.is_file() and sha(p)==expected,rel
C=json.loads((W/'config.json').read_text())
assert sha(W/'candidate-fast_dots.rs')==C['candidate_fast_dots_sha256']
assert sha(W/'baseline-source-hashes.json')==C['baseline_source_hashes_sha256']
assert sha(W/'baseline-runs.json')==C['baseline_runs_sha256']
assert sha(W/'current-source-relevance.json')==C['current_source_relevance_sha256']
assert sha(W/'verifier-strict-stack.py')==C['strict_stack_script_sha256']
assert sha(W/'run-stage.py')==C['run_stage_sha256']
R=json.loads((W/'results/gate-result.json').read_text())
assert R['candidate_fast_dots_sha256']==C['candidate_fast_dots_sha256']
assert R['candidate_artifact_sha256']=='07dc7c5b77d6eae882f786fee18b8ab8ba922323d425f344a823e8f02e68fff1'
assert len(R['six_fixture_rows'])==6
assert all(x['stage1_checkpoint_tail_same'] and x['return_data_same'] for x in R['six_fixture_rows'])
assert all(x['stage1_delta']>0 and x['settlement_delta']>0 for x in R['six_fixture_rows'])
assert R['strict_stack_receipt']['exit_status']==0
assert max(max(x['candidate_stage1_cu'],x['candidate_settlement_cu']) for x in R['six_fixture_rows'])<=1_400_000
print('measurement evidence checks passed; candidate body reuse is pinned, fixtures finite, CU regressing')

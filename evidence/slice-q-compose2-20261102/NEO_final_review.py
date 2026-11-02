"""Evidence inventory and final co-import audit; never launches a prover."""
from pathlib import Path
import json,re,hashlib,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (E/'NEO_ACTIVE.json').exists()
attempts=[json.loads(s) for s in (E/'NEO_ATTEMPTS.jsonl').read_text().splitlines()]
counts=collections.Counter(d['kind'] for d in attempts);assert dict(counts)==dict(kani=80,lean=86,extract=10)
assert len({d['attempt'] for d in attempts})==176
rc=load(E/'NEO_L086/receipt.json');assert rc['exit_status']==0 and rc['swaps']=='0'
assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert len(rc['print_axioms'])==98
for line in rc['print_axioms']:
 m=re.search(r'axioms: \[([^]]*)\]',line);assert m,line
 assert {a.strip() for a in m[1].split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'},line
for f,h in rc['source_hashes'].items():assert sha(E/f)==h
for d in load(E/'NEO_FINAL_AUDIT_INPUTS.json'):
 for f,h in d['source_hashes'].items():assert sha(E/f)==h
for i in range(1,81):
 assert (E/f'NEO_K{i:03}/receipt.json').exists()
 assert (E/f'NEO_K{i:03}_INPUTS.json.xz').exists() and (E/f'NEO_K{i:03}_INPUTS.json.sha256').exists()
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024**2]
assert load(E/'NEO_TESTS_RECEIPT.json')['exit_status']==0 and load(E/'NEO_TESTS_RECEIPT.json')['tests']==34
d=load(E/'NEO_LEDGER_DELTA.json');assert (d['total_closed'],d['q_closed'],d['edge_closed'])==(130,108,124)
assert set(d['roots'].values())=={'OPEN'}
remaining=load(E/'NEO_REMAINING.json');assert len(remaining['remaining_functions'])==24 and len(remaining['remaining_edges'])==133
out=dict(target='NEO_final_review.py',exit_status=0,budget_used=dict(counts),budget_limit=dict(kani=80,lean=100,extract=10),lean_unused=14,lean_unused_reason='All independently actionable model/reference/Result/window/frame obligations attempted and compiled; remaining24 function frontiers require new native heap/caller/result evidence, missing outside-Q native bridges or owner adoption. Extra wrappers would assume the missing native fact. See NEO_REMAINING.json and NEO_LeanContinuation.md.',axioms_audited=98,coimport_modules=48,coimport_receipt='NEO_L086/receipt.json',coimport_exit=rc['exit_status'],coimport_wall_seconds=rc['wall_seconds'],coimport_peak_rss_kib=rc['peak_rss_kib'],coimport_swaps=rc['swaps'],coimport_source_revision=rc['source_revision'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,composed_rows_closed=130,q_occurrences_closed=108,q_functions_closed=54,edges_closed=124,roots='OPEN',security_target_established=False,authoritative_baseline_unchanged=True,validator_sha256=sha(E/'NEO_validate.py'),tests_sha256=sha(E/'NEO_tests.py'),report_sha256=sha(E/'NEO_COMPOSED.md'))
(E/'NEO_FINAL_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))

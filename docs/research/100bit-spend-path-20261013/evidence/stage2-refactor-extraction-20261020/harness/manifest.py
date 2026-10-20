#!/usr/bin/env python3
"""Index retained run receipts and evidence pins; no build or test execution."""
from pathlib import Path
import hashlib,json,subprocess
B=Path(__file__).resolve().parent.parent
rows=json.loads((B/'runs.json').read_text())
required=['gate-codec-complete-inputs','gate-counter-adopted','gate-counter-audit-eight-way','gate-program-lib-inputs-complete','gate-crate-default','gate-crate-detail','gate-pool-default','gate-pool-r1-features','gate-pool-all-features','gate-pool-v7-candidate','gate-teeth-inputs-complete','gate-authenticated-tx2','sbf-verifier-refactor','stack-verifier-refactor','gate-r1p-retry']+['cu-'+k+'-'+str(n) for k in ['transfer','withdrawal'] for n in [13,255,1023]]
byname={r['run']:r for r in rows}
assert all(n in byname and byname[n]['exit_status']==0 for n in required)
r=json.loads((B/'r1p-retry-gate.json').read_text());assert r['accepted']>=8 and r['accepted_proofs_verified_strict_and_dense']>=8 and r['retry_loop']['verified_strict_and_dense']
cu=json.loads((B/'cu.json').read_text());assert len(cu['rows'])==6 and all(r['stage1_ok'] and r['settlement_ok'] for r in cu['rows'])
assert json.loads((B/'stack-audit.json').read_text())['gate_pass']
files={str(p.relative_to(B)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(B.rglob('*')) if p.is_file() and p.name!='manifest.json'}
m=dict(schema='stage2-refactor-extraction-v1',classification='VERIFIER SOURCE CHANGE',source_base_revision=json.loads((B/'pins/source-hashes.json').read_text())['base_revision'],refactor_required_gates=required,refactor_gates_pass=True,extraction_status='not started',first_facts_status='not started',runs=rows,files=files,print_axioms='N/A: no Lean compilation in refactor stage',open=['R13/R12 refinement','R15 checkpoint provenance/canonicality','R19 all-input oracle/first-read bound','S8 and analytical CU re-pin'])
if (B/'manifest.json').exists():
    prior=json.loads((B/'manifest.json').read_text())
    for k in ['refactor_source_revision','extraction_status','first_facts_status','extraction']:
        if k in prior:m[k]=prior[k]
(B/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Refactor manifest checked:',len(required),'required successful runs')

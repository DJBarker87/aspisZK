#!/usr/bin/env python3
"""Audit existing sampler source cuts and checked theorem receipts; no new theorem."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';A=D/'evidence/qm31-index-sampler-extraction-20261016/input'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((A/'source-pins.json').read_text());cuts=[]
for cut in pins['declaration_cuts']:
 old=subprocess.check_output(['git','show',pins['source_revision']+':'+cut['path']],cwd=R).decode()
 fragment=''.join(old.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']])
 assert hashlib.sha256(fragment.encode()).hexdigest()==cut['sha256']
 current=R/cut['path'];matches=fragment in current.read_text()
 cuts.append(dict(**cut,current_file_sha256=sha(current),exact_cut_still_present=matches))
assert all(c['exact_cut_still_present'] for c in cuts)
source='crates/aspis-r1-cost-probe/src/sampler.rs';assert sha(R/source)==pins['source_files'][source]
status=D/'evidence/soundness-env-20261020/status.jsonl';names=['ExtractedQM31SamplerPassLoop','ExtractedQM31SamplerDivision','ExtractedQM31SamplerCorrect','ExtractedDigest32SamplerTransport'];proofs=[]
for line in status.read_text().splitlines():
 row=json.loads(line)
 if row['module'] not in names:continue
 receipt=row['reused_receipt'];assert receipt['exit']==0
 p=R/receipt['repo_source'];assert sha(p)==row['source_sha256']==receipt['source_sha256']
 proofs.append(dict(module=row['module'],proof_source=receipt['repo_source'],source_sha256=sha(p),status_file=str(status.relative_to(R)),status_file_sha256=sha(status),source_revision=row['source_revision'],deps_fingerprint=row['deps_fingerprint'],receipt=receipt))
assert len(proofs)==len(names)
out=dict(source_checkpoint='9c131667ca00f4daae78da6299b09a9fe0d00da9',archive_source_pins=str((A/'source-pins.json').relative_to(R)),archive_source_pins_sha256=sha(A/'source-pins.json'),exact_source_cuts=cuts,entire_sampler_source_unchanged=True,sampler_sha256=sha(R/source),eligible_checked_theorems=proofs,qualification='Existing whole division-pass and sampler total/canonical/value theorems are eligible on identical source cuts. This audit does not compile a transport into ProverRwCaller/ProverRwSampler, bind all external models, certify the whole per-attempt body, or discharge conjunct 1.',lowering_delta='Fresh optimized extraction uses wrapping integer operations; retained proved extraction uses checked operations. Source cut identity does not discharge the bounded checked/wrapping transport.',new_lean_compiles=0,new_nominal_transport_checked=False,whole_leaf_gate_complete=False)
p=D/'evidence/prover-rw-20261023/continuation/reused-sampler-proofs.json';p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(exact_cuts=len(cuts),checked_modules=len(proofs),entire_sampler_source_unchanged=True,new_nominal_transport_checked=False)))

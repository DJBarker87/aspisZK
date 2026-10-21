#!/usr/bin/env python3
"""Aggregate retained attempts without treating partial checks as S7 closure."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s7-kani-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rust=[json.loads(p.read_text()) for p in sorted((E/'receipts').glob('*/receipt.json'))]
lean=[dict(packet=str(p.parent.relative_to(E)),**json.loads(p.read_text())) for p in sorted((E/'proofs').glob('*/receipt.json'))]
preflight=[json.loads(p.read_text()) for p in sorted((E/'proofs').glob('*/preflight.json'))]
for attempt in rust:
 if attempt['exit_status']==124:
  attempt['rss_measurement_limit']='GNU time may undercount descendants not reaped after timeout; no exact aggregate RSS was collected. 8 GiB cgroup limit was enforced; zero swap enforced. Do not use wrapper RSS as descendant peak.'
selected=['scalar-extracted-01','scalar-proof-04','loop-simulation-01','row-contract-01','query-read-03','stored-node-02']
accepted=[r for r in lean if Path(r['packet']).name in selected]
assert len(accepted)==6
axioms=[]
for r in accepted:
 assert r['exit_status']==0 and r['source_sha256']==sha(B/'lean'/(r['module']+'.lean'))
 for report in r['print_axioms']:
  assert not any(s in report for s in ['sorryAx','_ax','ofReduceBool'])
  m=re.search(r'axioms:\s*\[([^\]]*)\]',report)
  if m:assert set(s.strip() for s in m[1].split(','))<={'propext','Classical.choice','Quot.sound'}
  axioms.append(report)
assert len(axioms)==13
summary=dict(schema='s7-owned-p6-partial-certificate-v1',status='PARTIAL; S7 and deployed R17 caller residual OPEN',premises_removed=[],accepted_lean_modules=[r['module'] for r in accepted],axiom_audits=axioms,accepted_kani_attempts=['kani-06','kani-09','kani-11'],kani_harnesses_passed=30,additional_geometry_harness='kani-02 geometry_query_offset_correspondence: passed; enclosing batch failed after row review stop',native_reference_tests=3,full_reference_translation='charon-06 and aeneas-06 exit 0',complete_emitted_cone_kernel_checked=False,full_runtime_correspondence_proved=False,shipped_source_changes=[],lean_peak_rss_bytes=max(r['peak_rss_bytes'] for r in accepted),zero_swap_all_accepted=all(r['swaps']==0 for r in accepted),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),proof_manifest='manifest.json')
(E/'accepted-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',rust_or_translation_attempts=rust,lean_attempts=lean,preflight_failures=preflight),indent=2)+'\n')
print(f'{len(rust)} host attempts, {len(lean)} Lean attempts; 13 accepted audits; 30 accepted Kani harnesses; S7 remains OPEN')

#!/usr/bin/env python3
"""Audit local text receipts without replaying unchanged expensive gates."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/ct-kernels-v2-20261022'
source=json.loads(subprocess.check_output(['python3',str(R/'tools/ct-kernels-20261022/v2-source-audit.py')],cwd=R))
(E/'source-audit.json').write_text(json.dumps(source,indent=2)+'\n')
receipts={p.parent.name:json.loads(p.read_text()) for p in (E/'receipts').glob('*/receipt.json')}
assert len(receipts)==16
for n,r in receipts.items():
 assert r['exit_status']==(101 if n=='v2-pole-regression' else 0),(n,r['exit_status'])
 assert r['swaps']==0 and r['cgroup_swap_peak_bytes']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['wall_seconds']>0 and r['peak_rss_kib']>0 and 'N/A' in r['print_axioms']
 for p in source['production_allowlist']:
  assert r['source_sha256'][p]==hashlib.sha256((R/p).read_bytes()).hexdigest(),(n,p)
 if n.startswith('v2-kani-'):
  assert 'Complete - 1 successfully verified harnesses, 0 failures, 1 total.' in (E/'receipts'/n/'stdout.log').read_text(),n
for p in E.glob('reservation-*.json'):
 r=json.loads(p.read_text());assert r['allowed'] and r['all_populated_scopes_bounded'] and r['bounded_reserved_bytes']+r['requested_bytes']<=r['safe_limit_bytes']
pins=['40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0','12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']
elf=json.loads((E/'elf-identities.json').read_text());assert len(elf)==3
for r,pin in zip(elf,pins):assert r['sha256']==r['expected_sha256']==pin and r['byte_equal'] and r['exit_status']==0
fixture=json.loads((E/'fixture-identities.json').read_text());assert fixture['proof_and_public_byte_identity'] and fixture['features']=='optimized-terminal,ct-host-prover'
for r in fixture['fixtures']:assert r['native_acceptance'] and r['dense_acceptance'] and r['proof_bytes']==57607 and r['public_bytes']==1880
metadata=json.loads((E/'host-metadata.json').read_text());assert metadata['native_binary_sha256']==fixture['binary_sha256'] and metadata['tls_values_and_check_times_symbols_absent'] and metadata['core_ct_feature_resolved']
reg=(E/'receipts/v2-pole-regression-lib/stdout.log').read_text()
assert 'no_pole_is_lean_no_pole_transfer ... ok' in reg and 'no_pole_is_lean_no_pole_withdrawal ... ok' in reg
notes=dict(failed_scope_attempt=dict(attempt='v2-pole-regression',exit_status=101,reason='Unscoped cargo test also compiled shared_point_contraction_equivalence, whose unrelated tools/r1-shared-point-candidate/weights.baseline.rs is absent from the host subset',replacement='v2-pole-regression-lib: changed scope --lib, exit 0'),refused_elf_launch=dict(command='python3 tools/ct-kernels-20261022/elf-host.py v2',exit_status=1,reason='Copied historical receipt elf-v2-default already exists; host-run.py O.mkdir refused before executing the SBF build',build_executed=False,wall_peak_swap='N/A: refused before measured child command',replacement='elf-v2final-default/devnet/pool: fresh v2 receipts, all exit 0'),native_trace_repeat_reason='v2-pole-native-final strengthens test assertions for the first active pole and all-inactive masks; no unchanged native rerun',source_labels='Early dirty labels are disambiguated by per-attempt source SHA-256; every receipt matches the committed production source hashes')
(E/'attempt-notes.json').write_text(json.dumps(notes,indent=2)+'\n')
summary=json.loads((E/'summary.json').read_text());summary.update(status='PASS: accepted local compositional/source gates; no whole-prover L2/L3 claim',failed_attempts=['v2-pole-regression'],symbolic_gates=6,accepted_final_gate_receipts=14,supplementary_native_receipts=1,failed_scope_receipts=1)
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
result=dict(exit_status=0,production_hashes_match_all_receipts=True,symbolic_gates=6,elf_pins_match=True,fixture_proof_and_public_bytes_match=True,resource_reservations_and_caps_valid=True,zero_swaps=True,failed_attempt_preserved=True,print_axioms='N/A: no Lean')
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(E))+'\n' for p in sorted(E.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
print(json.dumps(result))

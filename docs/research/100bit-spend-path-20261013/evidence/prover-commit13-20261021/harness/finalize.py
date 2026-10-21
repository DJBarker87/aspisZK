#!/usr/bin/env python3
"""Freeze text/hash evidence only; never launches a proof or build."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
accepted={r['name'] for r in json.loads((E/'validation.json').read_text()) if r.get('status')=='accepted'}
assert len(accepted)==20
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 pin=json.loads((E/(name+'-inputs.json')).read_text())
 rows.append(dict(target=name,adopted_certificate=name in accepted,source_revision=pin['source_revision'],source_pins=name+'-inputs.json',exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_memory_peak_bytes=r['cgroup_memory_peak_bytes'],swaps=r['swaps'],command=r['command'],limits=r['limits'],axioms='N/A: Rust/translation evidence; not a Lean theorem',receipt=str(p.relative_to(E))))
(E/'attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
lean=[json.loads(line) for p in sorted((E/'lean').glob('attempts-*.jsonl')) for line in p.read_text().splitlines()]
assert {r['attempt'] for r in lean}==set(range(8364,8373))
final=next(r for r in lean if r['attempt']==8372)
assert final['exit_status']==0 and len(final['axioms'])==6
new_sources=['ProverCommitAdmittedEndpoint','ProverCommitScalarPartition','ProverCommit13Audit']
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
source_pins={str(P/(n+'.lean')):hashlib.sha256((P/(n+'.lean')).read_bytes()).hexdigest() for n in new_sources}
report=Path('docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT13-20261021.md')
assert not subprocess.check_output(['git','diff','--name-only','9f6852af9','--','crates','programs','Cargo.toml','Cargo.lock'],text=True).strip()
assert not json.loads((E/'host-quiescence.json').read_text())['own_build_processes']
artifacts={}
for p in sorted(E.rglob('*')):
 if not p.is_file() or p.name=='manifest.json':continue
 assert p.suffix not in ['.olean','.llbc','.so','.a','.tar','.gz','.elf'],p
 artifacts[str(p.relative_to(E))]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
x=dict(branch='codex/cx-prover-commit13-20261021',base_revision='9f6852af9',build_recorded_revision=final['source_revision'],source_identity='Recorded revision plus literal additive source SHA-256 pins; final evidence committed after replay',source_pins=source_pins,report=dict(path=str(report),sha256=hashlib.sha256(report.read_bytes()).hexdigest()),release_target_established=False,all_family_coverage_closed=False,discharged=['builder_premises only at explicit canonical admitted-domain specialization'],quantifier_change='input fixed to BuilderSource.prover, canonical M31 public/witness RspendPlus instance',retained=['R_wire_builder_checker_D75_retry','G_sim_R_wire','actual Rust source identification','successful source-seed returned-material transport','complete material/D/packing/tree/retry shared-oracle transport'],original_arbitrary_input_endpoint_unchanged=True,rust_certificates=sorted(accepted),excluded_rust_and_translations=[r['target'] for r in rows if not r['adopted_certificate']],lean_attempts=lean,final_replay=final,next_env_J_attempt=8373,artifacts=artifacts)
(E/'manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print('Frozen 20 Rust certificates, 9 Lean attempts, one final replay; outer privacy target remains open.')

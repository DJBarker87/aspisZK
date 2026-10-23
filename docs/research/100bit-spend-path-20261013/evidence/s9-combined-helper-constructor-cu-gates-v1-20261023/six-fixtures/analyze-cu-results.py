from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent.parent
ATTEMPT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
base_dir = Path('lean-candidates/s4-const-generic-slot-candidate-v1-20261022/results/baseline')
baseline = json.loads((base_dir / 'cu.json').read_text())
baseline_runs_path = base_dir / 'runs.json'
source_pins = json.loads((base_dir / 'baseline-source-hashes.json').read_text())
prior = json.loads((ROOT / 'attempt3/evidence/current-source-gates/gates/gate-result.json').read_text())
raw = json.loads((ATTEMPT / 'remote-receipts/cu-result-v2.json').read_text())
rows = []
for measured in raw['six_fixture_rows']:
    fixture = measured['fixture']
    b = next(x for x in baseline if x['fixture'] == fixture)
    old = next(x for x in prior['six_fixture_rows'] if x['fixture'] == fixture)
    row = {
        'fixture': fixture,
        'approved_baseline_stage1_cu': b['stage1_cu'],
        'approved_baseline_settlement_cu': b['settlement_cu'],
        'legacy_b1_stage1_cu': b['b1_stage1'],
        'legacy_b1_settlement_cu': b['b1_settlement'],
        'helper933_stage1_cu': old['stage1_cu'],
        'helper933_settlement_cu': old['settlement_cu'],
        'combined_stage1_cu': measured['stage1_cu'],
        'combined_settlement_cu': measured['settlement_cu'],
        'delta_vs_approved_baseline_stage1': measured['stage1_cu'] - b['stage1_cu'],
        'delta_vs_approved_baseline_settlement': measured['settlement_cu'] - b['settlement_cu'],
        'delta_vs_legacy_b1_stage1': measured['stage1_cu'] - b['b1_stage1'],
        'delta_vs_legacy_b1_settlement': measured['settlement_cu'] - b['b1_settlement'],
        'increment_vs_helper933_stage1': measured['stage1_cu'] - old['stage1_cu'],
        'increment_vs_helper933_settlement': measured['settlement_cu'] - old['settlement_cu'],
        'approved_12000_pass': measured['stage1_cu'] <= b['stage1_cu'] + 12000 and measured['settlement_cu'] <= b['settlement_cu'] + 12000,
        'remaining_headroom_pass': measured['stage1_cu'] - old['stage1_cu'] <= 1183 and measured['settlement_cu'] - old['settlement_cu'] <= 3901,
        'outputs_match': measured['stage1_checkpoint_tail_same'] and measured['return_data_same'],
        'run_receipt': measured['run_receipt'],
        'candidate_evidence_sha256': measured['candidate_evidence_sha256'],
        'inputs_sha256': measured['input_artifact_and_proof_sha256'],
    }
    rows.append(row)

result = {
    'classification': 'post-run comparison audit; no additional fixture execution; candidate not adopted/deployed',
    'approved_policy': 'S4-ADOPTION-DECISION-20261022 permits <=12000 additional CU per transaction against the retained frozen b272 baseline. It explicitly reuses baseline/cu.json stage1_cu and settlement_cu; b1_* are kept as separate legacy strict-B1 fields.',
    's4_decision_path': 'docs/research/100bit-spend-path-20261013/design/S4-ADOPTION-DECISION-20261022.md',
    'baseline_source_revision': source_pins['source_revision'],
    'baseline_source_hash_manifest_sha256': sha(base_dir / 'baseline-source-hashes.json'),
    'baseline_runs_sha256': sha(baseline_runs_path),
    'baseline_cu_sha256': sha(base_dir / 'cu.json'),
    'baseline_cost_probe_artifact_path': '/home/dombarker/project-offloads/codex-cx-pin-20261020/artifacts/default/aspis_r1_cost_probe_program.so',
    'baseline_cost_probe_artifact_sha256_observed_on_nuc': 'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34',
    'baseline_artifact_hash_caveat': 'The retained baseline-runs entries pin the b272 revision and artifact path, but do not record the artifact SHA at execution time; the SHA above is an observation of that path on 2026-10-23.',
    'helper933_artifact_sha256': prior['candidate_artifact_sha256'],
    'combined_candidate_weights_sha256': raw['candidate_weights_sha256'],
    'combined_candidate_source_manifest_sha256': raw['source_manifest_sha256'],
    'combined_candidate_artifact_sha256': raw['candidate_artifact_sha256'],
    'raw_attempt26_runner_result_sha256': sha(ATTEMPT / 'remote-receipts/cu-result-v2.json'),
    'admission_receipt_sha256': sha(ATTEMPT / 'remote-receipts/admission-six-fixture-cu-v2.json'),
    'reservation_receipt_sha256': sha(ATTEMPT / 'remote-receipts/reservation-six-fixture-cu-v2.json'),
    'all_six_approved_12000_pass': all(x['approved_12000_pass'] for x in rows),
    'all_six_remaining_headroom_pass': all(x['remaining_headroom_pass'] for x in rows),
    'all_six_outputs_match': all(x['outputs_match'] for x in rows),
    'all_six_legacy_strict_b1_pass': all(x['combined_stage1_cu'] <= x['legacy_b1_stage1_cu'] and x['combined_settlement_cu'] <= x['legacy_b1_settlement_cu'] for x in rows),
    'rows': rows,
}
out = ATTEMPT / 'approved-comparison-v1.json'
out.write_text(json.dumps(result, indent=2) + '\n')
md = [
    '# Attempt 26 six-fixture CU comparison', '',
    'This is a comparison audit of already completed attempt 26 outputs. The authorized S4 comparator is the retained frozen-baseline `stage1_cu` / `settlement_cu` pair in `results/baseline/cu.json`; `b1_stage1` / `b1_settlement` remain separately reported historical strict-B1 values.', '',
    '| Fixture | Baseline stage1 / settle | Legacy B1 stage1 / settle | Helper933 stage1 / settle | Combined stage1 / settle | Delta vs approved baseline | Delta vs helper933 |',
    '|---|---:|---:|---:|---:|---:|---:|'
]
for x in rows:
    md.append(f"| {x['fixture']} | {x['approved_baseline_stage1_cu']} / {x['approved_baseline_settlement_cu']} | {x['legacy_b1_stage1_cu']} / {x['legacy_b1_settlement_cu']} | {x['helper933_stage1_cu']} / {x['helper933_settlement_cu']} | {x['combined_stage1_cu']} / {x['combined_settlement_cu']} | +{x['delta_vs_approved_baseline_stage1']} / +{x['delta_vs_approved_baseline_settlement']} | +{x['increment_vs_helper933_stage1']} / +{x['increment_vs_helper933_settlement']} |")
md += ['', f"All six approved +12,000 checks: **{result['all_six_approved_12000_pass']}**. All six headroom checks (1,183 stage1 / 3,901 settlement): **{result['all_six_remaining_headroom_pass']}**. Outputs match: **{result['all_six_outputs_match']}**. Legacy strict B1 all-pass: **{result['all_six_legacy_strict_b1_pass']}**.", '',
       f"Baseline revision: `{result['baseline_source_revision']}`; baseline-source manifest SHA256 `{result['baseline_source_hash_manifest_sha256']}`; retained `cu.json` SHA256 `{result['baseline_cu_sha256']}`. The referenced baseline cost-probe artifact currently hashes to `{result['baseline_cost_probe_artifact_sha256_observed_on_nuc']}` on the NUC; the historical runner record pins its path/revision but not an execution-time artifact digest.", '',
       f"Combined weights SHA256 `{result['combined_candidate_weights_sha256']}`; SBF artifact SHA256 `{result['combined_candidate_artifact_sha256']}`; helper-only artifact SHA256 `{result['helper933_artifact_sha256']}`.", '']
(ATTEMPT / 'approved-comparison-v1.md').write_text('\n'.join(md))
print(json.dumps({k:result[k] for k in ['all_six_approved_12000_pass','all_six_remaining_headroom_pass','all_six_outputs_match','all_six_legacy_strict_b1_pass']}))

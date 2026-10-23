#!/usr/bin/env python3
"""Verify the source-only S9 candidate CU evidence packet."""
from pathlib import Path
import hashlib, json, sys

ROOT = Path(__file__).resolve().parent

def read(rel):
    return json.loads((ROOT / rel).read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise SystemExit(f"FAIL: {message}")

# Source packet and manifest pins.
base = ROOT / 'source/weights-production-base.rs'
helper = ROOT / 'source/weights-helper933.rs'
combined = ROOT / 'source/weights-combined-constructor-v2.rs'
source_pins = read('source/source-pins.json')
require(sha(base) == '28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137', 'production base hash')
require(sha(helper) == '9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf', 'helper933 source hash')
require(sha(combined) == '241a4f7dfe57666576b7653556c09d3dedef8606cf02f4ac4cd4cddf5c7663f8', 'combined source hash')
require(source_pins['candidate_weights_sha256'] == sha(combined), 'source pin weights hash')
require(source_pins['weights_base_sha256'] == sha(helper), 'source pin helper base hash')
require(source_pins['research_head'] == '7998f6355d7163b5df1550f3440041b5b79dd48b', 'candidate source revision')
stack = read('source/stack-audit.json')
require(stack['weights_sha256'] == sha(combined), 'stack audit source hash')
require(stack['candidate_artifact_sha256'] == '603af510fca0a54209d6950d814256af257cb8da4e239bbb73e25e01daeb64a2', 'stack artifact hash')
require(stack['constructor_stack_diagnostic'] is False and stack['pack_helper_stack_diagnostic'] is False, 'constructor own-frame stack diagnostics')
require(stack['whole_program_stack_pass'] is False and stack['whole_program_stack_diagnostic_count'] == 34, 'whole-program stack caveat')

# Validate all packet file hashes. SHA256SUMS is deliberately generated last and excludes itself.
lines = (ROOT / 'SHA256SUMS').read_text().splitlines()
seen = set()
for line in lines:
    digest, rel = line.split('  ', 1)
    p = ROOT / rel
    require(p.is_file(), f'missing checksummed file {rel}')
    require(sha(p) == digest, f'checksum mismatch {rel}')
    require(rel not in seen, f'duplicate checksum entry {rel}')
    seen.add(rel)
for p in ROOT.rglob('*'):
    if p.is_file() and p.name != 'SHA256SUMS':
        require(str(p.relative_to(ROOT)) in seen, f'untracked packet file {p.relative_to(ROOT)}')
        require(p.suffix.lower() not in {'.so', '.bin', '.olean', '.key'}, f'forbidden binary/key artifact {p.relative_to(ROOT)}')
        require('keypair' not in p.name.lower() and 'proof.bin' not in p.name.lower() and 'public.bin' not in p.name.lower(), f'forbidden private/proof file {p.relative_to(ROOT)}')

# Six-fixture raw evidence and authorized baseline arithmetic.
comparison = read('six-fixtures/approved-comparison-v1.json')
raw = read('six-fixtures/raw/cu-result-v2.json')
baseline = read('six-fixtures/baselines/baseline-cu.json')
prior = read('six-fixtures/baselines/prior-helper933-gate-result.json')
baseline_by = {r['fixture']: r for r in baseline}
prior_by = {r['fixture']: r for r in prior['six_fixture_rows']}
raw_by = {r['fixture']: r for r in raw['six_fixture_rows']}
comparison_by = {r['fixture']: r for r in comparison['rows']}
expected = {'transfer-1023','transfer-13','transfer-255','withdrawal-1023','withdrawal-13','withdrawal-255'}
require(set(raw_by) == expected and set(comparison_by) == expected and set(baseline_by) == expected and set(prior_by) == expected, 'six fixture names')
require(raw['candidate_weights_sha256'] == sha(combined), 'CU source pin')
require(raw['candidate_artifact_sha256'] == stack['candidate_artifact_sha256'], 'CU artifact pin')
require(sha(ROOT/'six-fixtures/raw/cu-result-v2.json') == comparison['raw_attempt26_runner_result_sha256'], 'raw CU-result SHA in comparison')
require(sha(ROOT/'six-fixtures/raw/admission-six-fixture-cu-v2.json') == comparison['admission_receipt_sha256'], 'admission SHA in comparison')
require(sha(ROOT/'six-fixtures/raw/reservation-six-fixture-cu-v2.json') == comparison['reservation_receipt_sha256'], 'reservation SHA in comparison')
require(comparison['baseline_cu_sha256'] == sha(ROOT/'six-fixtures/baselines/baseline-cu.json'), 'baseline CU hash')
require(comparison['baseline_runs_sha256'] == sha(ROOT/'six-fixtures/baselines/baseline-runs.json'), 'baseline runs hash')
require(comparison['all_six_approved_12000_pass'] is True, 'approved policy pass aggregate')
require(comparison['all_six_remaining_headroom_pass'] is True, 'incremental headroom aggregate')
require(comparison['all_six_outputs_match'] is True, 'output match aggregate')
require(comparison['all_six_legacy_strict_b1_pass'] is False, 'legacy strict-B1 remains a separate fail')
for name in sorted(expected):
    rawrow, cmp = raw_by[name], comparison_by[name]
    fixture_dir = 'cu-' + name
    candidate_ev = read(f'six-fixtures/raw/fixtures/{fixture_dir}/evidence.json')
    helper_ev = read(f'six-fixtures/raw/helper933-evidence/{fixture_dir}/evidence.json')
    require(sha(ROOT/f'six-fixtures/raw/fixtures/{fixture_dir}/evidence.json') == rawrow['candidate_evidence_sha256'], f'{name} raw evidence hash')
    require(sha(ROOT/f'six-fixtures/raw/helper933-evidence/{fixture_dir}/evidence.json') == prior_by[name]['candidate_evidence_sha256'], f'{name} helper evidence hash')
    ce = candidate_ev['execution']; he = helper_ev['execution']; b = baseline_by[name]; h = prior_by[name]
    stage = ce['stage1_compute_units']; settle = ce['compute_units']
    require(rawrow['run_receipt']['exit_status'] == 0 and rawrow['run_receipt']['timed_out'] is False, f'{name} raw execution success')
    require(rawrow['run_receipt']['swap_current_bytes'] == 0 and rawrow['run_receipt']['limits']['memory.swap.max'] == '0', f'{name} swap policy')
    require(stage == rawrow['stage1_cu'] and settle == rawrow['settlement_cu'], f'{name} current raw CU fields')
    require(he['stage1_compute_units'] == h['stage1_cu'] and he['compute_units'] == h['settlement_cu'], f'{name} helper933 raw CU fields')
    require(ce['stage1_checkpoint_tail_sha256'] == he['stage1_checkpoint_tail_sha256'], f'{name} stage1 output equality')
    require(ce['return_data_sha256'] == he['return_data_sha256'], f'{name} terminal output equality')
    require(stage == cmp['combined_stage1_cu'] and settle == cmp['combined_settlement_cu'], f'{name} comparison source values')
    require(stage - b['stage1_cu'] == cmp['delta_vs_approved_baseline_stage1'], f'{name} stage1 approved delta')
    require(settle - b['settlement_cu'] == cmp['delta_vs_approved_baseline_settlement'], f'{name} settlement approved delta')
    require(stage - h['stage1_cu'] == cmp['increment_vs_helper933_stage1'], f'{name} stage1 helper delta')
    require(settle - h['settlement_cu'] == cmp['increment_vs_helper933_settlement'], f'{name} settlement helper delta')
    require(stage <= b['stage1_cu'] + 12000 and settle <= b['settlement_cu'] + 12000, f'{name} approved +12000 test')
    require(cmp['approved_12000_pass'] and cmp['remaining_headroom_pass'] and cmp['outputs_match'], f'{name} approved/headroom/output booleans')
    require(cmp['remaining_headroom_pass'] == (cmp['increment_vs_helper933_stage1'] <= 1183 and cmp['increment_vs_helper933_settlement'] <= 3901), f'{name} remaining headroom math')

admission = read('six-fixtures/raw/admission-six-fixture-cu-v2.json')
require(admission['checks']['finite_plus_cap_le_48GiB'] and admission['checks']['finite_plus_cap_uncapped_usage_and_os_reserve_le_MemTotal'] and admission['checks']['available_after_cap_reserve_ge_14GiB'], 'attempt26 fresh admission passed')
require(admission['scope_high_bytes'] == 2*1024**3 and admission['scope_max_bytes'] == 4*1024**3 and admission['swap_max_bytes'] == 0, 'attempt26 H2/Max4/Swap0')
denied = read('admission-denied/attempt25-admission.json')
require(denied['checks']['finite_plus_cap_le_48GiB'] is False and denied['scope_max_bytes'] == 12*1024**3, 'attempt25 H10/Max12 denial preserved')

# Full-OS-mask one-sample control; the reused proof is not a fresh draw in this run.
fm = read('full-osmask/full-mask-result.json')
evidence = read('full-osmask/evidence.json')
command = read('full-osmask/command.json')
receipt = read('full-osmask/receipt.json')
prov = read('full-osmask/original-corpus-provenance.json')
require(fm['proof_reused'] is True and fm['fresh_mask_draw_in_this_run'] is False, 'full-mask proof reuse limitation')
require(prov['original_fixture']['mask_mode'] == 'full-mask' and prov['original_fixture']['mask_entropy_option'] == 'os', 'original proof OS full-mask provenance')
require(prov['inventory_row']['proof_sha256'] == fm['proof_sha256'] == command['input_hashes']['proof_sha256'], 'full-mask proof identity')
require(prov['inventory_row']['public_sha256'] == fm['public_sha256'] == command['input_hashes']['public_sha256'], 'full-mask public identity')
require(command['argv'][-3] == '--reuse' and command['argv'][6:8] == ['transfer','success'], 'full-mask accepted transfer route')
require(fm['candidate_artifact_sha256'] == stack['candidate_artifact_sha256'] == receipt['candidate_artifact_sha256'], 'full-mask candidate ELF identity')
require(evidence['execution']['stage1_compute_units'] == 1206885 and evidence['execution']['stage1_serialized_transaction_bytes'] == 295, 'full-mask stage1 leg')
require(fm['execution']['compute_units'] == 1148259 and fm['execution']['serialized_transaction_bytes'] == 882, 'full-mask terminal transaction leg')
require(fm['execution']['compute_units'] == evidence['execution']['compute_units'] and evidence['execution']['error'] is None, 'full-mask terminal accepted')
require(receipt['exit_status'] == 0 and receipt['swap_current_bytes'] == 0 and receipt['limits']['memory.swap.max'] == '0', 'full-mask run resource result')
require(receipt['limits']['memory.high'] == str(512*1024**2) and receipt['limits']['memory.max'] == str(1024**3), 'full-mask H512MiB/Max1GiB')
require('one sample' in fm['classification'] and 'worst-case' in fm['classification'], 'one-sample classification')

print('PASS: source pins, source-only inventory, six raw fixture rows, approved comparator/headroom, outputs, attempt25 denial, and both full-mask transaction legs/provenance')

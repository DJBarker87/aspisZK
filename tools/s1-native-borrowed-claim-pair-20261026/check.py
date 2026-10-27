#!/usr/bin/env python3
"""Audit source-only profile evidence; do not infer whole-source closure."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

R = Path(__file__).resolve().parents[2]
D = Path(__file__).resolve().parent
E = R / 'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
O = E / 's1-native-borrowed-claim-profile-terminal-v1'
N = O / 'native'
load = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def function(text, name):
    start = text.index('fn ' + name + '(')
    end = text.index('{', start) + 1
    depth = 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end]

# Both profiles assert the same complete leaf arguments/state transitions.
# This is a source identity check, not a proof installing the actual leaves.
prior = (R / 'tools/s1-native-prepared-claim-20261025/proofs.rs').read_text()
current = (D / 'profile.rs').read_text()
common = ['same_e', 'same_q', 'mul_stub', 'same_dot', 'push_stub',
          'finish_stub', 'field_stub', 'add_stub', 'any_q', 'any_row',
          'any_challenges', 'any_e']
for name in common:
    assert function(prior, name) == function(current, name), name
original_audit = json.loads(subprocess.check_output([
    'python3', str(R / 'tools/s1-native-prepared-claim-20261025/check.py')],
    cwd=R, text=True))
assert original_audit['status'] == 'PASS'
binding = load(N / 'paired-binding.json')
assert binding['zero_copy_reference']
assert sha(D / 'reference-zero-copy.rs') == binding['reference_sha256']
assert sha(D / 'profile.rs') == binding['proof_sha256']
assert (N / 'min/src/prepared_claim_native/proofs.rs').read_text() == current
native = (N / 'min/src/prepared_claim_native/verifier.rs').read_text()
assert (D / 'reference-zero-copy.rs').read_text() in native
extraction = O / 'extraction'
eb = load(extraction / 'binding.json')
assert sha(R / eb['base_source']) == eb['base_sha256']
assert sha(extraction / 'input/lib.rs') == eb['candidate_sha256']
assert sha(D / 'reference-zero-copy.rs') == eb['new_reference_sha256']
assert (extraction / 'input/lib.rs').read_text() == (
    (R / eb['base_source']).read_text().replace(
        (D / 'reference.rs').read_text(),
        (D / 'reference-zero-copy.rs').read_text(), 1))
for phase in ['charon', 'aeneas']:
    a = extraction / ('run-' + phase)
    r = load(a / 'receipt.json')
    assert r['exit_status'] == 0 and r['swaps'] == 0
    assert r['source_unchanged'] and r['tools_unchanged']
    assert r['cgroup']['memory.swap.max'] == '0'
    for name, expected in load(a / 'input.json')['source_pins'].items():
        assert sha(extraction / name) == expected, (phase, name)
assert load(extraction / 'run-charon/receipt.json')['llbc_sha256'] == load(
    extraction / 'run-aeneas/receipt.json')['llbc_sha256']
for name, row in load(O / 'zero-copy-model-reuse.json').items():
    old = E / 's1-native-borrowed-helper-20261024/historical-generated/AspisS1OwnedNestedClaim' / name
    new = extraction / 'generated/AspisS1OwnedNestedClaim' / (name + '.txt')
    assert sha(old) == row['historical_sha256']
    assert sha(new) == row['zero_copy_sha256']
    assert re.sub(r'/--[\s\S]*?-/', '', old.read_text()) == re.sub(
        r'/--[\s\S]*?-/', '', new.read_text())
frozen = subprocess.check_output([
    'git', 'show', binding['release_revision'] +
    ':crates/aspis-r1-cost-probe/src/verifier.rs'], cwd=R, text=True)
assert binding['original_claim'] in frozen and binding['original_claim'] in native

rows = []
for point in [0, 1, 2, 3, 4, 6]:
    a = N / ('run-point' + str(point))
    receipt = load(a / 'verify-receipt.json')
    inputs = load(a / 'verify-input.json')
    assert receipt['exit_status'] == 0
    assert receipt['source_unchanged'] and receipt['tools_unchanged']
    assert receipt['swaps'] == 0
    assert receipt['cgroup']['memory.swap.max'] == '0'
    assert int(receipt['cgroup']['memory.max']) == 8 * 2**30
    assert '--unwinding-assertions' in receipt['command']
    assert '-C opt-level=3' in inputs['environment']['RUSTFLAGS']
    for name, expected in inputs['source_pins'].items():
        path = N / name
        if name == 'nuc.py' and sha(path) != expected:
            matches = [p for p in N.glob('nuc.py.v*') if sha(p) == expected]
            assert len(matches) == 1, (point, name)
        else:
            assert sha(path) == expected, (point, name)
    post = a / 'linked-loop-postcheck.json'
    if point == 6:
        post = N / 'run-postcheck6/linked-loop-postcheck.json'
    post = load(post)
    assert post['exit_status'] == 0 and post['all_four_checked_loop_ids_present']
    assert post['verified_command'] == receipt['command']
    log = (a / 'verify-stdout.log').read_text()
    assert 'VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION SUCCESSFUL' in log
    rows.append(dict(point=point, wall_seconds=receipt['wall_seconds'],
                     peak_rss_kib=receipt['peak_rss_kib'], swaps=0))

failed = N / 'run-point5'
failure = load(failed / 'verify-receipt.json')
assert failure['exit_status'] != 0 and failure['swaps'] == 0
assert failure['source_unchanged'] and failure['tools_unchanged']
assert 'CBMC timed out' in (failed / 'verify-stdout.log').read_text()
assert 'oom_kill 0' in failure['cgroup']['memory.events']
negative = N / 'run-negative'
assert load(negative / 'verify-receipt.json')['exit_status'] != 0
assert 'Failed Checks: assertion failed: !negative' in (negative / 'verify-stdout.log').read_text()
for name, row in load(O / 'manifest.json')['files'].items():
    assert sha(O / name) == row, name
assert not any(p.suffix in {'.olean', '.llbc', '.out', '.rlib', '.so'}
               for p in O.rglob('*') if p.is_file())
print(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    status='PASS', accepted_profiles=rows,
    remaining_reference_partitions=[5],
    excluded_timeout=failure,
    exact_shared_leaf_guard_functions=common,
    checked_original_profile_partitions=original_audit['accepted_claim_partitions'],
    remaining_original_profile_partitions=original_audit['remaining_claim_partitions'],
    native_original_reference_paired_proof=False,
    actual_leaf_installation_proved=False,
    enclosing_s1_closed=False, enclosing_s6_closed=False), indent=2))

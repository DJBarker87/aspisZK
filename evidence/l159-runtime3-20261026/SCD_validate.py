"""Validate focused proof receipts, exact retained signature, unchanged Rc5 recount."""
from pathlib import Path
import hashlib
import json
import re

E = Path(__file__).resolve().parent
R = E.parents[1]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
receipts = [json.loads((E / f'SCD_{i:03}/receipt.json').read_text()) for i in range(1, 4)]
assert [r['exit_status'] for r in receipts] == [0, 0, 0]
limits = {'memory.high': '6442450944', 'memory.max': '8589934592',
          'memory.swap.max': '0', 'pids.max': '64'}
for r in receipts:
    assert r['limits'] == limits and r['swaps'] == '0'
    assert '-M7000' in r['command'] and '-j1' in r['command']
    assert r['print_axioms']
    for line in r['print_axioms']:
        assert 'sorryAx' not in line
        names = set(re.search(r'\[([^\]]*)\]', line)[1].split(', '))
        assert names <= {'propext', 'Classical.choice', 'Quot.sound'}
    for name, digest in r['source_hashes'].items():
        assert sha(E / r['attempt'] / 'sources' / name) == digest
        assert sha(R / 'lean' / name) == digest
    reservation = json.loads((E / (r['attempt'] + '-reservation.json')).read_text())
    assert reservation['allowed']
    assert reservation['requested_bytes'] == 8 * 2**30
    assert reservation['projected_reserved_bytes'] < reservation['safe_limit_bytes']
    for obj in r['deps_fingerprint']['selected_objects'].values():
        assert len(obj['sha256']) == 64 and obj['bytes'] > 0
for name in ['SCD_Carrier.lean', 'SCD_ExactTop.lean', 'SCD_Nonvacuity.lean']:
    p = R / 'lean' / name
    code = re.sub(r'/\-.*?\-/', '', p.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code)
    assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)', code)
for name, digest in json.loads((E / 'SCD_HOST_SOURCES.json').read_text()).items():
    p = R / ('tools/s2w-20261023' if name.endswith('.py') else 'lean') / name
    assert sha(p) == digest, name
for name, row in json.loads((E / 'SCD_ADMISSION_SOURCES.json').read_text()).items():
    assert sha(R / 'docs/research/100bit-spend-path-20261013/lean' / name) == row['sha256']
before = (E / 'SCD_BEFORE_Top.lean.txt').read_bytes()
assert before == (E / 'SCD_AFTER_Top.lean.txt').read_bytes()
assert before == (R / 'lean/Rc5_Top.lean').read_bytes()
root = before.decode()
expected = root[root.index('theorem deployed'):root.index(' :\n    DrvC_Implementation.driver')]
expected = expected.replace('theorem deployed', 'theorem retained_context')
expected = expected.replace('    (runtime : F3T_Runtime.Runtime)\n', '')
start = expected.index('    (binding : F3T_Runtime.StoredCarrierBinding')
end = expected.index('    (adversary :', start)
expected = expected[:start] + expected[end:]
new = (R / 'lean/SCD_ExactTop.lean').read_text()
actual = new[new.index('theorem retained_context'):new.index(' :\n    ∃ (runtime')]
assert actual == expected, 'Retained Rc5 binder types or witnesses differ'
log = (E / 'SCD_002/stdout.log').read_text()
assert 'theorem AspisR1.Rc5_Top.deployed' in log
assert 'theorem AspisR1.SCD_ExactTop.retained_context' in log
assert 'F3T_Runtime.StoredCarrierBinding' in log
assert 'SCD_Top.deployed' not in log
fixture = (E / 'SCD_003/stdout.log').read_text()
assert 'RuntimeEntrypointAdmission' in fixture and 'admitted_game_with_unassociated' in fixture
ledger = json.loads((R / 'evidence/recount5-20261026/Rc5_premises.json').read_text())
delta = json.loads((E / 'SCD_LEDGER_DELTA.json').read_text())
assert sha(R / delta['baseline_path']) == delta['baseline_sha256']
assert delta['before'] == delta['after'] == ledger['counts']
assert not delta['removed'] and not delta['added'] and not delta['changed']
assert {r['id'] for r in delta['targeted_rows']} == {'L159', 'L185'}
for scope, counts in ledger['counts'].items():
    rows = ledger['rows']
    if scope.startswith('actual'):
        rows = [r for r in rows if r['scope'] == 'actual antecedent']
    elif scope.startswith('deduplicated'):
        rows = [r for r in rows if r['scope'] != 'deployment alias']
    elif scope != 'all retained audit rows':
        rows = [r for r in rows if r['scope'] == scope]
    if 'excluding approved game domain' in scope:
        rows = [r for r in rows if r.get('role') != 'approved game domain']
    assert len(rows) == counts['rows']
    assert {c: sum(r['classification'] == c for r in rows) for c in ['T', 'P', 'C']} == counts['classes']
    for owner, classes in counts['by_owner'].items():
        assert {c: sum(r['owner'] == owner and r['classification'] == c for r in rows)
                for c in ['T', 'P', 'C']} == classes
assert not json.loads((E / 'SCD_FINAL_PROCESSES.json').read_text())['matching_processes']
summary = dict(lean_attempts=3, kani_runs=0, dependency_builds=0,
               passed=[r['attempt'] for r in receipts],
               wall_seconds=sum(r['wall_seconds'] for r in receipts),
               peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts), swaps=0,
               new_theorems_standard_axioms=5, axiom_audit_lines=6,
               exact_nonbinding_Rc5_signature_preserved=True,
               actual_before=delta['before']['actual antecedent']['classes'],
               actual_after=delta['after']['actual antecedent']['classes'],
               actual_delta=delta['actual_delta'],
               unused_lean_budget=97, unused_kani_budget=10,
               stop_reason='Exact retained premises lack observer/submission association; explicit residual STOP',
               full_joint_crypto_fixture=False, target_established=False)
(E / 'SCD_VALIDATION.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))

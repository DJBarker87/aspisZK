"""Offline focused receipts and unchanged Rc5 atomic-family recount; no builds."""
from pathlib import Path
import hashlib
import json
import re

E = Path(__file__).resolve().parent
R = E.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipts = [json.loads((E / f'SCC_{i:03}/receipt.json').read_text()) for i in range(1, 4)]
assert [r['exit_status'] for r in receipts] == [1, 0, 0]
limits = {'memory.high': '6442450944', 'memory.max': '8589934592',
          'memory.swap.max': '0', 'pids.max': '64'}
for r in receipts:
    assert r['limits'] == limits and r['swaps'] == '0'
    assert '-M7000' in r['command'] and '-j1' in r['command']
    for name, digest in r['source_hashes'].items():
        assert sha(E / r['attempt'] / 'sources' / name) == digest
    if r['exit_status'] == 0:
        assert r['print_axioms']
        for line in r['print_axioms']:
            assert 'sorryAx' not in line
            names = set(re.search(r'\[([^\]]*)\]', line)[1].split(', '))
            assert names <= {'propext', 'Classical.choice', 'Quot.sound'}
for name in ['SCC_Physical.lean', 'SCC_Nonvacuity.lean']:
    p = R / 'lean' / name
    assert any(r['exit_status'] == 0 and r['source_hashes'].get(name) == sha(p)
               for r in receipts)
    code = re.sub(r'/\-.*?\-/', '', p.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code)
    assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)', code)
for name, digest in json.loads((E / 'SCC_HOST_SOURCES.json').read_text()).items():
    p = R / ('tools/s2w-20261023' if name.endswith('.py') else 'lean') / name
    assert sha(p) == digest, name
before = (E / 'SCC_BEFORE_Top.lean.txt').read_bytes()
assert before == (E / 'SCC_AFTER_Top.lean.txt').read_bytes()
assert before == (R / 'lean/Rc5_Top.lean').read_bytes()
assert before == (R / 'evidence/recount5-20261026/Rc5_017/sources/Rc5_Top.lean').read_bytes()
log = (E / 'SCC_003/stdout.log').read_text()
assert 'theorem AspisR1.Rc5_Top.deployed' in log
assert 'F3T_Runtime.StoredCarrierBinding' in log
assert len(receipts[-1]['print_axioms']) == 7
assert 'AspisR1.SCC_Nonvacuity.game_with_unassociated' in log
assert 'SCC_Top.deployed' not in log
ledger = json.loads((R / 'evidence/recount5-20261026/Rc5_premises.json').read_text())
delta = json.loads((E / 'SCC_LEDGER_DELTA.json').read_text())
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
summary = dict(lean_attempts=3, kani_runs=0, dependency_builds=0,
               excluded_failure='SCC_001: ambiguous original_eval name; recovery sorryAx excluded',
               passed=['SCC_002', 'SCC_003'],
               wall_seconds=sum(r['wall_seconds'] for r in receipts),
               peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts), swaps=0,
               new_theorems_standard_axioms=5, final_axiom_lines=7,
               actual_before=delta['before']['actual antecedent']['classes'],
               actual_after=delta['after']['actual antecedent']['classes'],
               actual_delta=delta['actual_delta'],
               unused_lean_budget=97, unused_kani_budget=10,
               stop_reason='Corrected physical association needs unapproved observation law; explicit task STOP',
               full_joint_crypto_fixture=False, target_established=False)
(E / 'SCC_VALIDATION.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))

"""Offline receipt/source/axiom/cap audit and unchanged actual-root recount."""
from pathlib import Path
import hashlib
import json
import re

E = Path(__file__).resolve().parent
R = E.parents[1]
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

receipts = [json.loads(p.read_text()) for p in E.glob('SCE_*/receipt.json')]
assert 0 < len(receipts) <= 100
limits = {'memory.high': '6442450944', 'memory.max': '8589934592',
          'memory.swap.max': '0', 'pids.max': '64'}
groups = json.loads((E / "SCE_SCOPE_GROUPS.json").read_text())["groups"]
green = {}
for r in receipts:
    assert r['limits'] == limits and r['swaps'] == '0'
    assert '-M7000' in r['command'] and '-j1' in r['command']
    assert len(r['sources']) == 1
    for name, digest in r['source_hashes'].items():
        assert name.startswith('SCE_') and name.endswith('.lean')
        assert sha(E / r['attempt'] / 'sources' / name) == digest
        if r['exit_status'] == 0:
            green[name, digest] = r['attempt']
    if r['exit_status'] == 0:
        for line in r['print_axioms']:
            assert 'sorryAx' not in line
            m = re.search(r'\[([^\]]*)\]', line)
            if m:
                assert set(m[1].replace('\n', ' ').replace(' ', '').split(',')) <= {
                    'propext', 'Classical.choice', 'Quot.sound'}
            else:
                assert 'does not depend on any axioms' in line
    reservations = [json.loads(p.read_text()) for p in E.glob(r['attempt'] + '-reservation*.json')]
    matching = [g for g in groups if r['attempt'] in g['actual_attempts']]
    for g in matching:
        reservations.append(json.loads((E / g['admission']).read_text()))
        reference = json.loads((E / g['reference_receipt']).read_text())
        assert r['cgroup'] == reference['cgroup']
    allowed = [p for p in reservations if p['allowed']]
    assert allowed, r['attempt']
    for p in allowed:
        assert p['requested_bytes'] == 8 * 2**30
        assert p['projected_reserved_bytes'] < p['safe_limit_bytes']
    for obj in r['deps_fingerprint']['selected_objects'].values():
        assert len(obj['sha256']) == 64 and obj['bytes'] > 0

manifest = json.loads((E / 'SCE_HOST_MANIFEST.json').read_text())
last = json.loads((E / 'SCE_100/receipt.json').read_text())
for obj in last['deps_fingerprint']['selected_objects'].values():
    name = Path(obj['path']).name
    if name.startswith('SCE_'):
        assert obj['sha256'] == manifest['objects'][name]['sha256']
modules = sorted((R / 'lean').glob('SCE_*.lean'))
for p in modules:
    assert sha(p) == manifest['sources'][p.name]['sha256']
    for theorem in re.findall(r'^theorem\s+([\w]+)', p.read_text(), flags=re.M):
        assert '#print axioms ' + theorem in p.read_text(), (p.name, theorem)
    assert (p.name, sha(p)) in green, 'No exact-current-source passing receipt: ' + p.name
    code = re.sub(r'/\-.*?\-/', '', p.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code), p.name
    assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)', code), p.name

before = (E / 'SCE_BEFORE_Top.lean.txt').read_bytes()
assert before == (E / 'SCE_AFTER_Top.lean.txt').read_bytes()
assert before == (R / 'lean/Rc5_Top.lean').read_bytes()
ledger = json.loads((R / 'evidence/recount5-20261026/Rc5_premises.json').read_text())
delta = json.loads((E / 'SCE_LEDGER_DELTA.json').read_text())
assert sha(R / delta['baseline_path']) == delta['baseline_sha256']
assert delta['before'] == delta['after'] == ledger['counts']
assert not delta['removed'] and not delta['added'] and not delta['changed']
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

summary = dict(lean_attempts=len(receipts), kani_runs=0, dependency_builds=0,
    passing_attempts=sum(r['exit_status'] == 0 for r in receipts),
    failed_attempts=[r['attempt'] for r in receipts if r['exit_status'] != 0],
    exact_current_modules=len(modules),
    wall_seconds=sum(r['wall_seconds'] for r in receipts),
    peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts), swaps=0,
    actual_before=delta['before']['actual antecedent']['classes'],
    actual_after=delta['after']['actual antecedent']['classes'], actual_delta=delta['actual_delta'],
    target_established=False, full_joint_crypto_fixture=False)
(E / 'SCE_VALIDATION.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))

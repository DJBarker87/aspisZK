#!/usr/bin/env python3
"""Mutation checks of ledger validation; no source/evidence is modified."""
import copy
import importlib.util
import json
from pathlib import Path
import resource
import subprocess
import time
from unittest import mock

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('ncz', HERE / 'NCZ_validate.py')
ncz = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ncz)
start = time.monotonic()
base = json.loads((HERE / 'NCZ_LEDGER.json').read_text())
results = []


def rejected(name, action):
    try:
        action()
    except (AssertionError, ValueError, KeyError, OSError) as e:
        results.append({'test': name, 'expected': 'reject', 'result': 'PASS',
                        'diagnostic': str(e)[:600]})
    else:
        raise AssertionError('validator accepted mutation: ' + name)


def mutate(name, change):
    d = copy.deepcopy(base)
    change(d)
    rejected(name, lambda: ncz.validate_invariants(d))


ncz.validate_invariants(base)
results.append({'test': 'unmodified ledger structural invariants', 'result': 'PASS'})
idx = next(i for i, r in enumerate(base['rows']) if r['bridge_status'] == 'CLOSED-CONDITIONAL')
mutate('CLOSED with an open named hypothesis', lambda d: d['rows'][idx].update(bridge_status='CLOSED'))
mutate('composed CLOSED with open caller domains', lambda d: d['rows'][idx].update(composed_status='CLOSED', named_hypotheses=[]))
mutate('conditional without a bridge certificate', lambda d: d['rows'][idx].update(selected_claims=[]))
p = next(iter(base['rows'][idx]['receipt_sha256']))
mutate('forged row receipt hash', lambda d: d['rows'][idx]['receipt_sha256'].update({p: '0'*64}))
mutate('missing cited evidence', lambda d: d['evidence_manifest'].pop(p))
qidx = next(i for i, r in enumerate(base['rows']) if r['bridge_status'] == 'quarantined')
mutate('quarantined bridge selected as conditional', lambda d: d['rows'][qidx].update(
    bridge_status='CLOSED-CONDITIONAL', selected_claims=[d['rows'][qidx]['claim_ids'][0]]))
selected = base['rows'][idx]['selected_claims'][0]
mutate('selected feature association contradicted', lambda d: next(c for c in d['claims'] if c['claim_id'] == selected).update(feature_parity='UNDETERMINED'))

store = ncz.Store()
p = ncz.INV[0][1]
try:
    oid = store.head_tree[p]
    store.head_tree[p] = '0'*40
    rejected('changed cited Git object including sparse paths', lambda: store.read(p))
    store.head_tree[p] = oid
    del store.head_tree[p]
    rejected('missing cited Git object including sparse paths', lambda: store.read(p))
    store.head_tree[p] = oid
    store.deleted.add(p)
    rejected('tracked materialized evidence deletion', lambda: store.read(p))
    store.deleted.remove(p)
    with mock.patch.object(ncz.Path, 'read_bytes', return_value=b'changed evidence'):
        rejected('changed present worktree evidence bytes', lambda: store.read(p))
    assert store.read(p) == (HERE.parent.parent / p).read_bytes()
    results.append({'test': 'unmodified Git/worktree evidence binding', 'result': 'PASS'})
finally:
    store.close()

created = []
class DriftStore(ncz.Store):
    def __init__(self):
        super().__init__()
        self.head_tree['evidence/new-merged-packet/NEW_FINDING.md'] = '0'*40
        created.append(self)
with mock.patch.object(ncz, 'Store', DriftStore):
    try:
        rejected('new merged evidence report cannot be silently ignored', ncz.collect)
    finally:
        for item in created:
            item.close()

usage = resource.getrusage(resource.RUSAGE_SELF)
receipt = {
    'target': 'NCZ_tests.py',
    'command': ['python3', 'evidence/native-compledger-20261028/NCZ_tests.py'],
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'source_tree_dirty': True,
    'source_sha256': ncz.sha(Path(__file__).read_bytes()),
    'validator_sha256': ncz.sha((HERE / 'NCZ_validate.py').read_bytes()),
    'ledger_sha256': ncz.sha((HERE / 'NCZ_LEDGER.json').read_bytes()),
    'dependency_fingerprint': ncz.sha(ncz.dump(base['evidence_manifest']).encode()),
    'exit_status': 0, 'wall_seconds': time.monotonic() - start,
    'peak_rss_bytes_macos': usage.ru_maxrss, 'swaps': usage.ru_nswap,
    'print_axioms': 'not applicable: Python evidence/mutation checks, no new Lean theorem',
    'cgroup': 'not applicable: read-only Python data validation, no Lean/Rust/Kani process',
    'lean_attempts': 0, 'kani_attempts': 0, 'tests': results,
    'external_file_mutations': 0}
(HERE / 'NCZ_TEST_RECEIPT.json').write_text(ncz.dump(receipt))
print(ncz.dump({'exit_status': 0, 'tests_passed': len(results),
                'wall_seconds': receipt['wall_seconds'],
                'peak_rss_bytes_macos': usage.ru_maxrss, 'swaps': usage.ru_nswap}))

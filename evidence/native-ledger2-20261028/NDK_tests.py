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
spec = importlib.util.spec_from_file_location('ncz', HERE / 'NDK_validate.py')
ncz = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ncz)
start = time.monotonic()
base = json.loads((HERE / 'NDK_LEDGER.json').read_text())
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
old_spec=importlib.util.spec_from_file_location('original_ncz',HERE.parent/'native-compledger-20261028'/'NCZ_validate.py')
original_ncz=importlib.util.module_from_spec(old_spec);old_spec.loader.exec_module(original_ncz)
original_ncz.validate_invariants(base)
results.append({'test':'unchanged NCZ invariants on refreshed ledger','result':'PASS'})
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

# New evidence kinds: run these gates directly on pinned examples, then mutate.
import NDK_review as review
mutate('forged recomputed coverage', lambda d: d['coverage']['TX1']['local_bridge_status'].update(OPEN=999))
mutate('dropped critical frontier representative', lambda d: d['critical_path']['frontier'].pop())
mutate('forged critical frontier dependent count', lambda d: d['critical_path']['frontier'][0].update(dependent_rows=0))
mutate('quarantined row silently downgraded to OPEN', lambda d: d['rows'][qidx].update(bridge_status='OPEN'))
mutate('model domain reported as native closure', lambda d: next(r for r in d['rows'] if 'model_caller_domain_progress' in r)['model_caller_domain_progress'].update(native_DriverEstablishedDomain='CLOSED'))
mutate('one residual checkpoint field group silently removed', lambda d: next(r for r in d['rows'] if 'model_caller_domain_progress' in r)['model_caller_domain_progress']['remaining_model_groups'].pop())
mutate('quarantined historical receipt promoted to active dependency', lambda d: next(c for c in d['claims'] if c['admissible_local_credit'] and c['historical_quarantined_receipts'])['active_support_receipts'].append(next(c for c in d['claims'] if c['admissible_local_credit'] and c['historical_quarantined_receipts'])['historical_quarantined_receipts'][0]))
store=ncz.Store()
try:
    dr='evidence/native-front1-20261028/'
    graph=store.obj(dr+'NDD_K007-graph-check.json')
    review.check_features(graph,'core-helper')
    bad=copy.deepcopy(graph);bad.pop('all_crate_features')
    rejected('missing all-crate feature record',lambda:review.check_features(bad,'core-helper'))
    bad=copy.deepcopy(graph);bad['all_crate_features']['aspis-statement'].remove('pool-v1-kernel')
    rejected('statement deployed kernel feature omitted',lambda:review.check_features(bad,'core-helper'))
    bad=copy.deepcopy(graph);bad['all_crate_features']['aspis-r1-cost-probe'].remove('optimized-terminal')
    rejected('verifier deployed optimized feature omitted',lambda:review.check_features(bad,'core-helper'))
    bad=copy.deepcopy(graph);fs=bad['all_crate_features']['aspis-statement'];fs.remove(next(x for x in fs if x.endswith('-audit')));fs.append('unrelated-audit')
    rejected('same-count wrong optimized features rejected',lambda:review.check_features(bad,'core-helper'))
    pg=store.obj('evidence/native-front4-20261028/NDG_K003-graph-check.json')
    review.check_features(pg,'program')
    bad=copy.deepcopy(pg)
    next(r for r in bad['selected_closure'] if r['name']=='aspis-r1-cost-probe-program')['features'].remove('pool-adapter')
    rejected('program root compiled without deployed adapter',lambda:review.check_features(bad,'program'))
    bad=copy.deepcopy(pg)
    next(r for r in bad['selected_closure'] if r['name']=='aspis-r1-cost-probe-program')['features'].append('no-entrypoint')
    rejected('program root compiled with no-entrypoint',lambda:review.check_features(bad,'program'))
    r=store.obj(dr+'NDD_K008/receipt.json');log=store.text(dr+'NDD_K008/stdout.log')
    review.check_native(r,log,False)
    bad=copy.deepcopy(r);bad['exit_status']=137
    rejected('killed control is not a negative',lambda:review.check_native(bad,log,False))
    rejected('compiler-only failure is not a semantic negative',lambda:review.check_native(r,'compiler failed',False))
    rejected('unmatched harness is not a negative',lambda:review.check_native(r,log+' Failed to match',False))
    rejected('multiple failure control rejected',lambda:review.check_native(r,log.replace('** 1 of','** 2 of'),False))
    r=store.obj(dr+'NDD_L007/receipt.json');src=store.read(dr+'NDD_Reduce.lean')
    review.check_theorem(r,'NDD_Reduce.reduce_cohort',src,src)
    bad=copy.deepcopy(r);bad['print_axioms'].append("'bad' depends on axioms: [sorryAx]")
    rejected('successful receipt with recovery sorryAx rejected',lambda:review.check_theorem(bad,'NDD_Reduce.reduce_cohort',src,src))
    rejected('changed passing theorem source rejected',lambda:review.check_theorem(r,'NDD_Reduce.reduce_cohort',src,src+b'-- changed'))
    rejected('unrelated theorem audit rejected',lambda:review.check_theorem(r,'NDD_Reduce.unrelated',src,src))
    recipe=json.loads((HERE/'NDK_ASSOCIATIONS.json').read_text())[0]
    row=store.obj(recipe['delta'])[recipe['delta_key']][recipe['index']]
    review.check_delta_association(recipe,row)
    bad=copy.deepcopy(recipe);bad['native'][0]['attempt']='NDD_K009'
    rejected('unrelated native PASS cannot support a different delta',lambda:review.check_delta_association(bad,row))
    results.append({'test':'pinned positive feature/native/theorem/delta gates','result':'PASS'})
finally:
    store.close()

usage = resource.getrusage(resource.RUSAGE_SELF)
receipt = {
    'target': 'NDK_tests.py',
    'command': ['python3', 'evidence/native-ledger2-20261028/NDK_tests.py'],
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'source_tree_dirty': True,
    'source_sha256': ncz.sha(Path(__file__).read_bytes()),
    'review_module_sha256': ncz.sha((HERE / 'NDK_review.py').read_bytes()),
    'original_ncz_validator_sha256': ncz.sha((HERE.parent / 'native-compledger-20261028' / 'NCZ_validate.py').read_bytes()),
    'validator_sha256': ncz.sha((HERE / 'NDK_validate.py').read_bytes()),
    'ledger_sha256': ncz.sha((HERE / 'NDK_LEDGER.json').read_bytes()),
    'dependency_fingerprint': ncz.sha(ncz.dump(base['evidence_manifest']).encode()),
    'exit_status': 0, 'wall_seconds': time.monotonic() - start,
    'peak_rss_bytes_macos': usage.ru_maxrss, 'swaps': usage.ru_nswap,
    'print_axioms': 'not applicable: Python evidence/mutation checks, no new Lean theorem',
    'cgroup': 'not applicable: read-only Python data validation, no Lean/Rust/Kani process',
    'lean_attempts': 0, 'kani_attempts': 0, 'tests': results,
    'external_file_mutations': 0}
(HERE / 'NDK_TEST_RECEIPT.json').write_text(ncz.dump(receipt))
print(ncz.dump({'exit_status': 0, 'tests_passed': len(results),
                'wall_seconds': receipt['wall_seconds'],
                'peak_rss_bytes_macos': usage.ru_maxrss, 'swaps': usage.ru_nswap}))

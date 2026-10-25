"""Focused offline source/import audit and historical counterfactual packet."""
import ast
import difflib
import hashlib
import json
import sys
from pathlib import Path
import ResourceStability_evaluator as policy
from ResourceStability_sources import c,go,blob,digest,ENTRY,AVAILABLE,DEPENDENCIES,ROOT
from ResourceStability_replay import replay_v2,data

OUT=ROOT/'evidence/resource-stability-20261025'
NUMERIC=('projected_reserved_bytes','min_mem_available_bytes','max_active_file_bytes',
    'max_kernel_withheld_bytes','max_root_residual_bytes','adjusted_available_bytes',
    'required_bytes','margin_bytes','cap_ok','available_ok','legacy_nonreserve_gate_ok')


def summary(decision):
    keys=('schema','allowed','error','adopted','phase','collector_identity',
          'membership_differences','collection_failures')+NUMERIC
    return {k:decision[k] for k in keys if k in decision}


def source_audit():
    original=blob('tools/resource-available-20261024/ResourceAvailable_go.py',AVAILABLE).decode()
    new=Path(policy.__file__).read_text()
    def function(text):
        return next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name=='evaluate')
    def numerical_suffix(fun):
        body=next(n for n in fun.body if isinstance(n,ast.Try)).body
        start=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='old_frontier')
        return [ast.dump(n,include_attributes=False) for n in body[start:]]
    assert numerical_suffix(function(original))==numerical_suffix(function(new))
    assert policy.observe is c.observe and policy.bind_scope is go.bind_scope
    assert go.membership is c.membership
    # Store reviewable exact before/after evaluator source diff, not a callback.
    diff=''.join(difflib.unified_diff(original.splitlines(True),new.splitlines(True),
        fromfile=AVAILABLE+':ResourceAvailable_go.py',tofile='ResourceStability_evaluator.py'))
    (OUT/'ResourceStability-evaluator.diff').write_text(diff)
    try:policy.read_only_admission(phase='prospective',additional_bytes=4*c.GIB)
    except RuntimeError as error:assert 'DISABLED' in str(error)
    else:raise AssertionError('live boundary enabled')
    return dict(numerical_suffix_AST_identical=True,unchanged_observe_and_bind_scope=True,
        old_evaluator_globals_unchanged=True,live_API='DISABLED',
        diff=digest(diff.encode()),print_axioms='N/A; no formal execution')


def counterfactual(actual,source):
    before,after=(actual['snapshots'][k] for k in ('before','after'))
    # Neither captured snapshot is modified, nor are old errors/decisions.
    pre=digest((json.dumps(actual,sort_keys=True,indent=2)+'\n').encode())
    decision=policy.evaluate(actual['original_legacy'],before,after,4*c.GIB,phase='prospective')
    assert pre==digest((json.dumps(actual,sort_keys=True,indent=2)+'\n').encode())
    for observation in (c.observe(before),c.observe(after)):
        assert observation['bounded_reserved_bytes']==26172456960
    result=dict(kind='COUNTERFACTUAL ONLY; no admission adoption',source_assessment=source,
        original_decision=summary(actual['decision']),new_policy=summary(decision),
        captured_API_object=pre,inputs_unchanged=True,
        collection_failures=actual['decision'].get('collection_failures',{}),
        actual_scoped_environment_established=False,live_API='DISABLED')
    return result


def dependency_and_input_inventory():
    # Hash immutable input blobs in the two historical packets, including old
    # failures/charges/receipts, without writing or editing any original path.
    paths=['evidence/resource-admit-20261024',
        'evidence/resource-available-20261024',
        'evidence/resource-stat-20261024/ASSESSMENT.md',
        'evidence/resource-stat-20261024/primary-source-hashes.json',
        'evidence/resource-hierarchy-20261024/SOURCE-ASSESSMENT.md']
    import subprocess
    names=subprocess.check_output(['git','ls-tree','-r','--name-only',ENTRY,*paths],cwd=ROOT,text=True).splitlines()
    for name in names:blob(name)
    local_dependencies={}
    for name,module in sorted(sys.modules.items()):
        path=getattr(module,'__file__',None)
        if path and Path(path).is_file() and Path(path).suffix in ('.py','.so'):
            local_dependencies[name]=dict(path=path,**digest(Path(path).read_bytes()))
    return dict(immutable_git_objects=dict(sorted(DEPENDENCIES.items())),
                local_imports=local_dependencies)


def main():
    source=source_audit()
    actual,replay=replay_v2()
    v2=counterfactual(actual,'NEW exact original v2 API replay of all14926 events; raw receipts retained in memory and original shards')
    expected_race=data('ResourceAdmit-race-detail-v2.json')
    changed=v2['new_policy']['membership_differences']
    membership_only=[dict(path=row['path'],fields={k:v for k,v in row['fields'].items() if k!='pids_current'})
                     for row in changed if set(row['fields'])-{'pids_current'}]
    assert membership_only==expected_race['changes']
    # Original race detail selected old membership() fields, which omit the
    # five hierarchical pids.current deltas. Retain and validate those too.
    counts=[row for row in changed if 'pids_current' in row['fields']]
    assert len(counts)==5
    assert all(row['fields']['pids_current']['before']-row['fields']['pids_current']['after']==1 for row in counts)
    assert policy.structural(actual['snapshots']['before'])==policy.structural(actual['snapshots']['after'])
    # Initial pair is reused from the independently audited bounded summary.
    # Do NOT rerun its unchanged old API/test suite or relabel its env failure.
    prefix='evidence/resource-admit-20261024/'
    initial=data('prospective-report-summary.json',prefix)
    old_receipt=data('actual-audit-receipt.json',prefix)
    raw=blob(prefix+'prospective-report-summary.json')
    assert digest(raw)==old_receipt['inputs']['prospective-report-summary.json']
    initial_result=counterfactual(initial,'REUSED initial14866-event audited summary inputs; historical causal replay NOT rerun; duplicated scanner receipts absent from summary')
    initial_result.update(old_scoped_env_failure='DENIED before GO; differing env field UNKNOWN; not relabelled',
        reused_audit_receipt=digest(blob(prefix+'actual-audit-receipt.json')),
        old_original_pins=data('export-receipt.json',prefix)['host_files'],
        source_revision_of_reused_audit=old_receipt['source_revision'])
    packet=dict(source_audit=source,original_v2_replay=replay,v2_counterfactual=v2,
        initial_reused_counterfactual=initial_result,live_API='DISABLED',adopted=False,
        both_security_targets='not established',Kani='59/60; final gate reserved',
        print_axioms='N/A; no proof/native/security obligations discharged')
    # Bounded summary only. Original >5MB objects are represented by hash+size.
    encoded=(json.dumps(packet,sort_keys=True,indent=2)+'\n').encode()
    assert len(encoded)<5_000_000
    (OUT/'ResourceStability-audit.json').write_bytes(encoded)
    inventory=dependency_and_input_inventory()
    (OUT/'ResourceStability-dependencies.json').write_text(json.dumps(inventory,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',original_v2_replay=replay,
        v2_counterfactual=summary(v2['new_policy']),
        initial_reused_counterfactual=summary(initial_result['new_policy']),
        live_API='DISABLED',print_axioms='N/A'),sort_keys=True))


if __name__=='__main__':main()

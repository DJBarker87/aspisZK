#!/usr/bin/env python3
"""Validate the narrowed matcher fix and paired diagnostics, not admission."""
from pathlib import Path
import hashlib,json
here=Path(__file__).resolve().parent;area=here.parents[1]
e=area/'evidence/cu-equivalence-20261019';d=e/'associated-types-diagnostic-a'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((d/'MANIFEST.json').read_text())
assert m['status']=='LOOP_BORROW_CHECK_FIXED_FULL_LIBRARY_ADMISSION_OPEN'
for name,pin in m['files'].items():
    p=d/name;assert sha(p)==pin['sha256'] and p.stat().st_size==pin['bytes'],name
build=json.loads((d/'build/receipt.json').read_text())
assert build['exit_status']==0 and build['process_swaps']==0
assert build['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
assert build['last_cgroup_observation']['memory.swap.current']=='0'
assert build['pins']['controller_sha256']==sha(here/'build-aeneas-associated-types.py')
assert build['pins']['patch_sha256']==sha(d/'build/associated-types.patch')
patch=(d/'build/associated-types.patch').read_text()
assert 'TTraitType _, TTraitType _' in patch
assert '&& phys_eq ty0 ty1 && ty_no_regions ty0 ->' in patch
assert 'AENEAS_IDENTICAL_ASSOCIATED_TYPES' in patch
assert 'loop_fixed_point_max_num_iters' not in patch
binary=build['binary_sha256'];runs={
    'array-deref-branch-join-a':1,'array-deref-loop-trace-a':1,
    'array-loop-isolated-a':2,'array-loop-borrow-diagnostic-a':1,
    'array-loop-borrow-diagnostic-b':2,'aeneas-associated-types-build-a':0,
    'array-loop-associated-types-a':0,'associated-types-regression-a':0,
    'array-associated-types-emission-a':1}
receipts={}
for name,exit_status in runs.items():
    r=json.loads((e/name/'receipt.json').read_text())
    assert r['exit_status']==exit_status and r['process_swaps']==0 and r['cgroup_swap_current']=='0',name
    assert not r['mandatory_review_stop'],name
    assert r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])<=8*2**30,name
    for key in ['command','source_revision','features','wall_seconds','peak_rss_kib','print_axioms']:assert key in r,name
    receipts[name]=sha(e/name/'receipt.json')
outer=json.loads((e/'aeneas-associated-types-build-a/receipt.json').read_text())
assert sum(item[1] for item in outer['reservations'])+8*2**30<=50*2**30
for name in ['array-loop-isolated-a','array-loop-borrow-diagnostic-a','array-loop-borrow-diagnostic-b']:
    r=json.loads((e/name/'receipt.json').read_text())
    assert sha(e/name/'diagnostic-source.py')==r['diagnostic_script_sha256'],name
r=json.loads((e/'array-loop-associated-types-a/receipt.json').read_text())
assert r['diagnostic_script_sha256']==sha(here/'diagnose-array-loop.py')
assert r['frontend_binary_sha256']==binary and r['env']['AENEAS_IDENTICAL_ASSOCIATED_TYPES']=='1'
before=(e/'array-loop-borrow-diagnostic-b/stderr.log').read_text()
assert 'match_rtys:' in before and before.count('TraitClause0::Output')>=2
after=(e/'array-loop-associated-types-a/stdout.log').read_text()
assert 'Crate successfully borrow-checked' in after
assert 'Could not compute a loop fixed point' not in after
summary=json.loads((d/'regression/summary.json').read_text())
assert summary['exit_status']==0 and len(summary['cases'])==14
assert summary['harness_sha256']==sha(here/'check-associated-type-emission.py')
for case in summary['cases']:
    assert case['passed'] and case['process_swaps']==0 and '-checks' in case['command']
    assert case['frontend_binary_sha256']==binary
    assert case['exit_status']==case.get('expected_exit',0)
    if 'expected_files' in case:assert case['actual_files']==case['expected_files']
    assert case==json.loads((d/'regression'/case['name']/'receipt.json').read_text())
full=(e/'array-associated-types-emission-a/stdout.log').read_text()
assert "The input arguments don't have the proper type" in full
assert 'expected 2 parent clauses, found 1' in full
assert 'Could not compute a loop fixed point' not in full
assert "Can't copy a mutable borrow" not in full
print(json.dumps(dict(status=m['status'],manifest_sha256=sha(d/'MANIFEST.json'),
    frontend_binary_sha256=binary,patch_sha256=build['pins']['patch_sha256'],
    run_receipt_sha256=receipts,regression_cases=14,array_library_source_admitted=False)))

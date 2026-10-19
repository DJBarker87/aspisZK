#!/usr/bin/env python3
"""Audit source-constraint normalization without inferring library admission."""
from pathlib import Path
import copy,hashlib,json
here=Path(__file__).resolve().parent;area=here.parents[1]
e=area/'evidence/cu-equivalence-20261019';d=e/'trait-constraints-diagnostic-a'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((d/'MANIFEST.json').read_text())
assert manifest['status']=='FULL_NORMALIZED_CRATE_BORROW_CHECKED_DICTIONARY_ADMISSION_OPEN'
for name,pin in manifest['files'].items():
    path=d/name;assert sha(path)==pin['sha256'] and path.stat().st_size==pin['bytes'],name
build=json.loads((d/'build/receipt.json').read_text())
assert build['exit_status']==0 and build['process_swaps']==0
assert build['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
assert build['last_cgroup_observation']['memory.swap.current']=='0'
assert build['pins']['controller_sha256']==sha(d/'build/controller-source.py')
assert build['pins']['helper_sha256']==sha(here/'aeneas-parent-projection-constraints.ml')
assert build['pins']['patch_sha256']==sha(d/'build/trait-constraints.patch')
helper=(here/'aeneas-parent-projection-constraints.ml').read_text()
for fragment in ['phys_eq equality.trait_ref tref','equality.type_id = type_id',
    'decl.generics.trait_type_constraints','constraint_.binder_regions <> []',
    'ty_no_regions equality.ty','AENEAS_PARENT_PROJECTION_CONSTRAINTS']:assert fragment in helper
receipts={}
for name,status in [('aeneas-trait-constraints-build-a',0),('array-trait-constraints-emission-a',1),('trait-constraints-regression-a',0)]:
    path=e/name/'receipt.json';r=json.loads(path.read_text())
    assert r['exit_status']==status and r['process_swaps']==0 and r['cgroup_swap_current']=='0'
    assert not r['mandatory_review_stop'] and r['limits']['memory.swap.max']=='0'
    receipts[name]=sha(path)
outer=json.loads((e/'aeneas-trait-constraints-build-a/receipt.json').read_text())
# The original controller omitted the extra container reservation. Preserve
# that exception explicitly; do not turn a successful build into a false
# compliant-resource claim. The replacement run verifies the identical pin.
assert sum(item[1] for item in outer['reservations'])+8*2**30>50*2**30
assert 'resource_review' in manifest
recheck=json.loads((d/'reservation-recheck/receipt.json').read_text())
assert recheck['resource_admission_verified'] and recheck['exit_status']==0
assert recheck['process_swaps']==0 and recheck['last_cgroup_observation']['memory.swap.current']=='0'
assert recheck['binary_sha256']==build['binary_sha256']
assert recheck['controller_sha256']==sha(here/'verify-aeneas-reservations.py')
assert sum(item[1] for item in recheck['reservations_at_compile_gate'])<=50*2**30
assert recheck['max_sampled_reservations_bytes']<=50*2**30
replacement=json.loads((e/'aeneas-trait-constraints-reservation-a/receipt.json').read_text())
assert replacement['exit_status']==0 and replacement['process_swaps']==0
assert replacement['limits']=={'memory.high':str(768*2**20),'memory.max':str(2**30),'memory.swap.max':'0'}
receipts['aeneas-trait-constraints-reservation-a']=sha(e/'aeneas-trait-constraints-reservation-a/receipt.json')
summary=json.loads((d/'regression/summary.json').read_text())
assert summary['exit_status']==0 and len(summary['cases'])==32
assert summary['harness_sha256']==sha(here/'check-trait-constraint-emission.py')
cases={case['name']:case for case in summary['cases']}
for name,case in cases.items():
    assert case['passed'] and case['process_swaps']==0 and '-checks' in case['command'],name
    assert case['frontend_binary_sha256']==build['binary_sha256'],name
    assert case['exit_status']==case.get('expected_exit',0),name
    assert case==json.loads((d/'regression'/name/'receipt.json').read_text()),name
    if 'expected_files' in case:assert case['actual_files']==case['expected_files'],name
    for file,pin in case['actual_files'].items():
        assert sha(d/'regression'/name/'generated'/case['namespace']/file)==pin,(name,file)
on=cases['full-library-borrow-constraints-1'];off=cases['full-library-borrow-constraints-0']
assert on['exit_status']==0 and off['exit_status']==2
assert on['input_llbc_sha256']==off['input_llbc_sha256']
assert on['env']['AENEAS_PARENT_PROJECTION_CONSTRAINTS']=='1'
assert off['env']['AENEAS_PARENT_PROJECTION_CONSTRAINTS']=='0'
assert 'Crate successfully borrow-checked' in (d/'regression'/on['name']/'stdout.log').read_text()
wrong=d/'regression/rejected-wrong_output/synthetic-negative.llbc'
removed=d/'regression/rejected-remove_output/synthetic-negative.llbc'
assert sha(wrong)==cases['rejected-wrong_output']['input_llbc_sha256']
assert sha(removed)==cases['rejected-remove_output']['input_llbc_sha256']
original=json.loads(wrong.read_text())
eqs=original['translated']['trait_decls'][7]['generics']['trait_type_constraints']
assert eqs[0]['skip_binder']['ty']=={'Untagged':{'TypeVar':{'Free':0}}}
eqs[0]['skip_binder']['ty']={'Untagged':{'TypeVar':{'Free':1}}}
encoded=(json.dumps(original,separators=(',',':'))+'\n').encode()
assert hashlib.sha256(encoded).hexdigest()==on['input_llbc_sha256']
assert hashlib.sha256(encoded).hexdigest()==cases['rejected-wrong_output']['original_input_sha256']
without=copy.deepcopy(original)
without['translated']['trait_decls'][7]['generics']['trait_type_constraints'].pop(0)
assert without==json.loads(removed.read_text())
for name in ['rejected-remove_output','rejected-wrong_output']:
    assert cases[name]['exit_status']==2
    logs=(d/'regression'/name/'stdout.log').read_text()+(d/'regression'/name/'stderr.log').read_text()
    assert "The input arguments don't have the proper type" in logs,name
full=(e/'array-trait-constraints-emission-a/stdout.log').read_text()
assert 'expected 2 parent clauses, found 1' in full
for gone in ["The input arguments don't have the proper type","Can't copy a mutable borrow",'Could not compute a loop fixed point']:assert gone not in full
print(json.dumps(dict(status=manifest['status'],manifest_sha256=sha(d/'MANIFEST.json'),
    frontend_binary_sha256=build['binary_sha256'],run_receipt_sha256=receipts,
    regression_cases=32,array_library_source_admitted=False)))

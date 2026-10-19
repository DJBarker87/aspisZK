#!/usr/bin/env python3
"""Audit guarded-reborrow diagnostics without inferring library admission."""
from pathlib import Path
import hashlib,importlib.util,json

here=Path(__file__).resolve().parent;area=here.parents[1]
evidence=area/'evidence/cu-equivalence-20261019'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
script=here/'normalize-deref-temporaries.py'
spec=importlib.util.spec_from_file_location('normalizer',script)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
runs={
 'deref-repro-charon-a':0,'deref-repro-aeneas-a':0,
 'deref-repro-charon-optimized-a':0,'deref-repro-aeneas-optimized-a':1,
 'deref-normalize-a':0,'deref-normalized-aeneas-a':0,
 'array-deref-normalize-a':0,'array-deref-normalized-aeneas-a':1,
 'deref-guard-regression-a':0}
receipts={}
for name,expected in runs.items():
    directory=evidence/name;r=json.loads((directory/'receipt.json').read_text())
    assert r['exit_status']==expected and r['process_swaps']==0 and r['cgroup_swap_current']=='0',name
    assert r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])<=8*2**30,name
    assert not r['mandatory_review_stop'],name
    for field in ['command','source_revision','features','wall_seconds','peak_rss_kib','print_axioms']:assert field in r,name
    receipts[name]=sha(directory/'receipt.json')
old=json.loads((evidence/'deref-normalize-a/receipt.json').read_text())
assert sha(evidence/'deref-normalize-a/normalizer-source.py')==old['normalizer_sha256']
library=json.loads((evidence/'array-deref-normalize-a/normalization.json').read_text())
assert library['normalizer_sha256']==sha(script) and len(library['changes'])==2
assert not library['rejected'] and library['ordinary_mutable_copy_check_disabled'] is False
assert library['rust_source_bodies_or_signatures_edited'] is False
assert library['llbc_bodies_rewritten'] is True
failed=(evidence/'array-deref-normalized-aeneas-a/stdout.log').read_text()+(evidence/'array-deref-normalized-aeneas-a/stderr.log').read_text()
assert "Can't copy a mutable borrow" not in failed
assert 'Could not compute a loop fixed point in 2 iterations' in failed
assert "The input arguments don't have the proper type" in failed
assert "try_trait.rs', lines 192:4-192:49" in failed
case_root=evidence/'deref-guard-regression-a/cases'
summary=json.loads((case_root/'summary.json').read_text())
assert summary['status']=='PASS_FRONTEND_REGRESSION_NOT_LIBRARY_ADMISSION'
assert summary['normalizer_sha256']==sha(script)
assert summary['harness_sha256']==sha(here/'check-deref-normalizer.py')
assert summary['original_input_sha256']==sha(here/'deref-repro-input/optimized.llbc')
assert summary['positive_matches_built_mir_byte_for_byte'] and summary['negative_copies_remain_rejected']
assert {c['case'] for c in summary['cases']}=={'positive','extra-use','named-local','intervening-write','source-storage-dead'}
for record in summary['cases']:
    name=record['case'];directory=case_root/name
    assert record==json.loads((directory/'receipt.json').read_text()),name
    assert record['process_swaps']==0 and '-checks' in record['command'],name
    assert record['normalizer_sha256']==sha(script),name
    assert record['input_sha256']==sha(directory/'input.llbc'),name
    assert record['normalized_sha256']==sha(directory/'normalized.llbc'),name
    actual,report=module.normalize(json.loads((directory/'input.llbc').read_bytes()))
    assert actual==json.loads((directory/'normalized.llbc').read_bytes()),name
    assert report==json.loads((directory/'normalization.json').read_bytes()),name
    positive=name=='positive'
    assert record['changed_functions']==([0,1] if positive else [1]),name
    assert record['exit_status']==(0 if positive else 1),name
    log=(directory/'stdout.log').read_text()+(directory/'stderr.log').read_text()
    if not positive:assert "Can't copy a mutable borrow" in log,name
    for file,pin in record['generated_lean'].items():
        assert sha(directory/'generated/AspisR1CuDeref'/file)==pin,(name,file)
    if positive:
        for file in ['Types.lean','Funs.lean']:
            assert (directory/'generated/AspisR1CuDeref'/file).read_bytes()==(here/'deref-repro-generated'/file).read_bytes()
print(json.dumps(dict(status='CHECKED_FRONTEND_REGRESSION_LIBRARY_ADMISSION_OPEN',
    run_receipt_sha256=receipts,regression_summary_sha256=sha(case_root/'summary.json'),
    library_normalization_sha256=sha(evidence/'array-deref-normalize-a/normalization.json'),
    normalizer_sha256=sha(script),array_library_source_admitted=False)))

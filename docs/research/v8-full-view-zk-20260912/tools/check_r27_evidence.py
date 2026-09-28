#!/usr/bin/env python3
"""Offline source/result integrity audit; no repeated expensive release gate."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r27-sparse-preparation'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
assert not any('keypair'in n or n.endswith(('.so','.regs','.insns'))for n in manifest)
expected={'sparse':[1626085,1627579],'shared':[1620236,1621719]}
proofs=['0f90e0670d5c7cedf1bea159640016eeec1574ac0de89dc94d83dd9255f07da7','ca868e8f9495e06368ecaa712486befecbfaadc6ab38e8caddf38e368134ca71']
for label,cus in expected.items():
    source=json.loads((e/label/'r18-stage.json').read_text());assert len(source['files'])==182 and 'r27_sparse_prepare'in source and 'r26_schoolbook_dot'not in source
    assert source['r27_sparse_prepare']['groups']==list(range(30))+[63]
    for n,h in source['files'].items():
        p=e/label/'source'/n
        if p.exists():assert sha(p)==h,n
    r=json.loads((e/label/'r24-svm-a/receipt.json').read_text());assert r['source_manifest_sha256']==sha(e/label/'r18-stage.json')and r['full_verifier']and not r['instrumented']
    for w,cu,proof in zip(r['runs'],cus,proofs):
        assert w['proof_sha256']==proof and len(w['results'])==4
        for x in w['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000:assert x['resource_failure']and not x['accepted']and not x['custom_rejection']
            elif x['case']=='honest':assert x['accepted']and x['cu']==cu
            else:assert x['custom_rejection']and not x['resource_failure']and not x['accepted']
    controls=json.loads((e/label/'r24-host-a/wire-controls/results.json').read_text());assert len(controls['cases'])==3281 and sum(x['checked_rejection']for x in controls['cases'])==3280
    log=(e/label/'r24-host-a/ordinary-check.log').read_text();assert 'R27_SPARSE source_vectors=256 tensor_coordinates=12032 poison_unused_coordinates=8448 genuine_public_inputs=2'in log
    log=(e/label/'r24-sbf-a/compile.log').read_text();assert 'overflows the maximum allowed frame'not in log and not('Stack offset'in log and'exceeded'in log)
tr=json.loads((e/'shared/full-trace/analysis.json').read_text());assert tr['exact_text_match']and tr['cu']==1620236 and tr['executed_instructions']==1513633
assert next(x['entries']for x in tr['functions']if 'QM31::mul::'in x['name'])==2171
for label,target,count in [('sparse-lean-pass','tools/R27SparseRead.lean',2),('boundary-lean-final','lean/AspisV8R19/FirstRelationBoundary.lean',8)]:
    meta=json.loads((e/label/'metadata.json').read_text());assert meta['exit']==0 and meta['source_sha256']==sha(root/target)
    log=(e/label/'compile.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count
binding=json.loads((e/'boundary-source/binding.json').read_text());source=json.loads((e/'shared/r18-stage.json').read_text())
assert len(binding['files'])==8 and not binding['beta_nonzero_assumed']and not binding['joint_image_existence_proved']
for n,v in binding['files'].items():assert v['in_full_source_manifest']and source['files'][n]==v['sha256']
review=json.loads((root/'R27_STATIC_REVIEW.json').read_text());assert not review['result']['require_another_tool_call_after_fixing']
print(json.dumps({'status':'PASS','artifacts':len(manifest),'selected_full_cu':expected['shared'],'pins':182,'actual_one_million_gate':'OPEN/resource failure','full_privacy_soundness_proved':False},indent=2))

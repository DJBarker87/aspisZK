#!/usr/bin/env python3
"""Offline integrity and gate audit. Does not repeat unchanged heavy tests."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r24-native'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((e/'MANIFEST.json').read_text())
for n,h in m.items():assert sha(e/n)==h,n
assert not any('keypair' in n or n.endswith(('.so','.regs','.insns'))for n in m)
expected={'compose-a':[2500981,2502249],'compose-b':[1857687,1859272],'compose-c':[1817965,1819559]}
for label,cus in expected.items():
    manifest=json.loads((e/label/'r18-stage.json').read_text())
    receipt=json.loads((e/label/'r24-svm-a/receipt.json').read_text())
    assert receipt['source_manifest_sha256']==sha(e/label/'r18-stage.json')
    assert receipt['full_verifier'] and receipt['scalar_transpose_installed'] and 'r24_profile' not in manifest
    for r,cu in zip(receipt['runs'],cus):
        assert len(r['results'])==4
        for x in r['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000:assert x['resource_failure'] and not x['accepted'] and not x['custom_rejection']
            elif x['case']=='honest':assert x['accepted'] and x['cu']==cu
            else:assert x['custom_rejection'] and not x['resource_failure'] and not x['accepted']
    checks=json.loads((e/label/'r24-host-a/wire-controls/results.json').read_text())
    assert len(checks['cases'])==3281 and sum(x['checked_rejection']for x in checks['cases'])==3280
    log=(e/label/'r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in log and not('Stack offset' in log and 'exceeded' in log)
best=json.loads((e/'compose-c/r18-stage.json').read_text())
assert len(best['files'])==176 and 'r24_inactive' in best and 'r24_packed' not in best
assert sha(root/'tools/r24_guarded_qm.rs')==best['files']['crates/aspis-core/src/r24_guarded_qm.rs']
for label in ['qm-c','inactive-a','packed-a-slower']:
    log=(e/label/'host/check.log').read_text()
    assert 'source_vectors=256 adjoint_basis_cases=4096 genuine_public_inputs=2' in log
    assert 'random_pairs=200000 boundary_pairs=1296' in log and 'checked_overflow_panics=15' in log
    for r in json.loads((e/label/'svm/receipt.json').read_text())['runs']:
        for x in r['results']:
            assert x['accepted'] if x['case']=='honest' else x['checked_rejection'] and not x['resource_failure']
lean=json.loads((e/'lean-b/metadata.json').read_text());assert lean['exit']==0 and sha(root/'tools/R24NativeBounds.lean')==lean['source_sha256']
log=(e/'lean-b/compile.log').read_text();assert 'sorryAx' not in log and log.count('depends on axioms:')==4
print(json.dumps({'status':'PASS','artifacts':len(m),'best_full_cu':expected['compose-c'],'one_million_gate':'OPEN/exhausted','formal_scope':'four arithmetic leaves, not source refinement or privacy'},indent=2))

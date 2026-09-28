#!/usr/bin/env python3
"""Offline exact-artifact gate audit; no unchanged expensive replay."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r24-followup'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((e/'MANIFEST.json').read_text())
for n,h in m.items():assert sha(e/n)==h,n
assert not any('keypair'in n or n.endswith(('.so','.regs','.insns'))for n in m)
expected={'full-d':[1734341,1736011],'simple-a':[1704310,1705674],'simple-b-slower':[1713454,1714868],'simple-c':[1690509,1691993]}
for label,cus in expected.items():
    source=json.loads((e/label/'r18-stage.json').read_text())
    assert len(source['files'])==(176 if label=='full-d'else 179)
    for n,h in source['files'].items():
        retained=e/label/'source'/n
        if retained.exists():assert sha(retained)==h,n
    r=json.loads((e/label/'r24-svm-a/receipt.json').read_text());assert r['source_manifest_sha256']==sha(e/label/'r18-stage.json')
    assert r['full_verifier'] and not r['instrumented']
    for w,cu in zip(r['runs'],cus):
        assert len(w['results'])==4
        for x in w['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000:assert x['resource_failure']and not x['accepted']and not x['custom_rejection']
            elif x['case']=='honest':assert x['accepted']and x['cu']==cu
            else:assert x['custom_rejection']and not x['resource_failure']and not x['accepted']
    controls=json.loads((e/label/'r24-host-a/wire-controls/results.json').read_text());assert len(controls['cases'])==3281 and sum(x['checked_rejection']for x in controls['cases'])==3280
    if label!='full-d':assert 'differential_cases=576 noncanonical_cases=7272 length_errors=2' in (e/label/'r24-host-a/dot-check.log').read_text()
best=json.loads((e/'simple-c/r18-stage.json').read_text());assert 'r24_reconstruct'in best and 'r24_prepared'in best and 'r24_inline'not in best
assert 'operations_per_pair=6 dot_arities=2,3,4'in(e/'reconstruct/host/check.log').read_text()
trace=json.loads((e/'full-d/full-trace/analysis.json').read_text());assert trace['exact_text_match']and trace['cu']==1734341 and trace['executed_instructions']==1627468
tr=json.loads((e/'full-d/full-trace/receipt.json').read_text());assert tr['clean_cu_equal'] and tr['elf_sha256']==trace['elf_sha256']
lean=json.loads((e/'lean/metadata.json').read_text());assert lean['exit']==0 and lean['source_sha256']==sha(root/'tools/R24Reconstruction.lean')
log=(e/'lean/compile.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==2
print(json.dumps({'status':'PASS','artifacts':len(m),'selected_full_cu':expected['simple-c'],'pins':179,'actual_one_million_gate':'OPEN/resource failure','privacy_soundness_completion':False},indent=2))

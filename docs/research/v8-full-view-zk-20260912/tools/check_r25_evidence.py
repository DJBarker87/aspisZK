#!/usr/bin/env python3
"""Audit retained R25 evidence without rerunning unchanged expensive gates."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r25-checked-dot'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((e/'MANIFEST.json').read_text())
for n,h in m.items():assert sha(e/n)==h,n
assert not any('keypair'in n or n.endswith(('.so','.regs','.insns'))for n in m)
expected={'checked-dot':[1672860,1674376],'reconstruction-width':[1647658,1649182],'reduction-array':[1637329,1638823]}
proofs=['0f90e0670d5c7cedf1bea159640016eeec1574ac0de89dc94d83dd9255f07da7','ca868e8f9495e06368ecaa712486befecbfaadc6ab38e8caddf38e368134ca71']
for label,cus in expected.items():
    source=json.loads((e/label/'r18-stage.json').read_text());assert len(source['files'])==180 and 'r25_checked_dot'in source
    for n,h in source['files'].items():
        path=e/label/'source'/n
        if path.exists():assert sha(path)==h,n
    r=json.loads((e/label/'r24-svm-a/receipt.json').read_text());assert r['source_manifest_sha256']==sha(e/label/'r18-stage.json')
    assert r['full_verifier'] and not r['instrumented'] and len(r['runs'])==2
    for w,cu,proof in zip(r['runs'],cus,proofs):
        assert w['proof_sha256']==proof and len(w['results'])==4
        for x in w['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000:assert x['resource_failure']and not x['accepted']and not x['custom_rejection']
            elif x['case']=='honest':assert x['accepted']and x['cu']==cu
            else:assert x['custom_rejection']and not x['resource_failure']and not x['accepted']
    controls=json.loads((e/label/'r24-host-a/wire-controls/results.json').read_text());assert len(controls['cases'])==3281 and sum(x['checked_rejection']for x in controls['cases'])==3280
    log=(e/label/'r24-host-a/dot-check.log').read_text();assert 'differential_cases=576 noncanonical_cases=7272 length_errors=2'in log
    if label!='checked-dot':assert 'R25_SMALL_DOT cases=600192 canonical_vectors=200064 arities=2,3,4'in log
    log=(e/label/'r24-sbf-a/compile.log').read_text();assert 'overflows the maximum allowed frame'not in log and not('Stack offset'in log and'exceeded'in log)
for label,entries,insns in [('checked-dot',501,1566017),('reconstruction-width',57,1540815),('reduction-array',57,1530486)]:
    tr=json.loads((e/label/'full-trace/analysis.json').read_text());assert tr['exact_text_match'] and tr['cu']==expected[label][0] and tr['executed_instructions']==insns
    r=json.loads((e/label/'full-trace/receipt.json').read_text());assert r['clean_cu_equal'] and r['elf_sha256']==tr['elf_sha256']
    h=json.loads((e/label/'full-trace/helper-callers.json').read_text());assert h['helper_entries']==entries and h['elf_sha256']==tr['elf_sha256']
lean=json.loads((e/'lean/metadata.json').read_text());assert lean['exit']==0 and lean['source_sha256']==sha(root/'tools/R25CanonicalSum.lean')
log=(e/'lean/compile.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==2
assert sha(root/'tools/r25_checked_dot.rs')==json.loads((e/'checked-dot/r18-stage.json').read_text())['files']['crates/aspis-core/src/r25_checked_dot.rs']
print(json.dumps({'status':'PASS','artifacts':len(m),'full_cu':expected,'actual_one_million_gate':'OPEN/resource failure','privacy_soundness_completion':False},indent=2))

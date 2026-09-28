#!/usr/bin/env python3
"""Retained-artifact checks for the actual assembled schoolbook-dot experiment."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r26-schoolbook-dot'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
assert not any('keypair'in n or n.endswith(('.so','.regs','.insns'))for n in manifest)
expected={'array':[1669196,1670584],'unrolled':[1671116,1672504],'lane-major':[1980821,1982209]}
control=root/'evidence/r25-checked-dot/reduction-array'
control_receipt=json.loads((control/'r24-svm-a/receipt.json').read_text())
for label,cus in expected.items():
    m=json.loads((e/label/'r18-stage.json').read_text());assert len(m['files'])==180 and 'r26_schoolbook_dot'in m
    for n,h in m['files'].items():
        path=e/label/'source'/n
        if path.exists():assert sha(path)==h,n
    receipt=json.loads((e/label/'r24-svm-a/receipt.json').read_text());assert receipt['source_manifest_sha256']==sha(e/label/'r18-stage.json')
    assert receipt['full_verifier'] and not receipt['instrumented'] and len(receipt['runs'])==2
    assert [w['proof_sha256']for w in receipt['runs']]==[w['proof_sha256']for w in control_receipt['runs']]
    for w,cu in zip(receipt['runs'],cus):
        assert len(w['results'])==4
        for x in w['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000:assert x['resource_failure']and not x['accepted']and not x['custom_rejection']
            elif x['case']=='honest':assert x['accepted']and x['cu']==cu
            else:assert x['custom_rejection']and not x['resource_failure']and not x['accepted']
    c=json.loads((e/label/'r24-host-a/wire-controls/results.json').read_text());assert len(c['cases'])==3281 and sum(x['checked_rejection']for x in c['cases'])==3280
    log=(e/label/'r24-host-a/dot-check.log').read_text();assert 'differential_cases=576 noncanonical_cases=7272 length_errors=2'in log and 'R25_SMALL_DOT cases=600192'in log
    log=(e/label/'r24-sbf-a/compile.log').read_text();assert 'overflows the maximum allowed frame'not in log and not('Stack offset'in log and'exceeded'in log)
tr=json.loads((e/'array/full-trace/analysis.json').read_text());assert tr['exact_text_match']and tr['cu']==1669196 and tr['executed_instructions']==1562353
r=json.loads((e/'array/full-trace/receipt.json').read_text());assert r['clean_cu_equal']and r['elf_sha256']==tr['elf_sha256']
lean=json.loads((e/'lean-pass/metadata.json').read_text());assert lean['exit']==0 and lean['source_sha256']==sha(root/'tools/R26SchoolbookDot.lean')
log=(e/'lean-pass/compile.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==3
failed=(e/'lean-failed/compile.log').read_text();assert 'Unknown constant `Finset.mul_sum`'in failed and 'Exit status: 1'in failed
lengths=json.loads((e/'array/full-trace/dot-lengths.json').read_text());assert lengths['entries']==65 and lengths['length_histogram']=={'4':1,'5':33,'6':17,'16':4,'27':10}
callers=json.loads((e/'control-callers/qm-callers.json').read_text());assert callers['elf_sha256']==control_receipt['elf_sha256']and callers['helper_entries']==2269 and sum(x['calls']for x in callers['callers'])==2269
print(json.dumps({'status':'PASS','artifacts':len(manifest),'full_cu':expected,'actual_one_million_gate':'OPEN/resource failure','full_privacy_soundness_proved':False},indent=2))

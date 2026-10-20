#!/usr/bin/env python3
"""Assemble the D99/P6 route from retained solver receipts and kernel proofs."""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sha=lambda b:hashlib.sha256(b).hexdigest()
old=json.loads((HERE/'builder-cont3-evidence/kani-and-extraction.json').read_text())
coverage=json.loads((HERE/'builder-cont3-evidence/records-field-coverage.json').read_text())
names=list(coverage['harness_fields'])
assert len(names)==6
assert coverage['coverage']==coverage['required']
harness=(ROOT/'tools/r1-builder-reference/records.rs').read_bytes()
receipts={}
for name in names:
    r=old['kani'][name]
    assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in r['result']
    pins=r['source_pins']; checks={}
    for name0,pin in pins.items():
        p=ROOT/name0
        if not p.exists(): continue
        b=p.read_bytes()
        if sha(b)==pin: checks[name0]='exact'
        else:
            assert name0=='tools/r1-builder-reference/records.rs',name0
            ends=[i+1 for i,x in enumerate(b) if x==10]
            prefix=next((i for i in ends if sha(b[:i])==pin),None)
            assert prefix, 'historical harness must be a byte-exact prefix'
            checks[name0]=dict(exact_prefix_bytes=prefix,current_bytes=len(b),
                appended_only=True,old_sha256=pin,current_sha256=sha(b))
    receipts[name]={k:r[k] for k in ['command','exit_status','wall_seconds','peak_rss_kib','swaps','stdout_sha256','stderr_sha256']}
    receipts[name]['source_checks']=checks
attempts=[json.loads(x) for x in (HERE/'builder-cont6-attempts.jsonl').read_text().splitlines()]
modules=['BuilderRecordsArray','BuilderRecordsMatrix','BuilderRecordsRecipient','BuilderRecordsPublic','BuilderRecordsPath','BuilderRecordsReference','BuilderRecordsP6']
final={}
for m in modules:
    p=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{m}.lean'
    r=next(r for r in reversed(attempts) if r['module']=='R1Z.'+m and r['exit']==0 and r['source_sha256']==sha(p.read_bytes()))
    names0=re.findall(r'^#print axioms (.+)$',p.read_text(),re.M)
    assert len(r['axioms'])==len(names0),(m,names0,r['axioms'])
    for a in r['axioms']:
        assert 'sorryAx' not in a
        if 'depends on axioms:' in a:
            assert set(a.split('[')[1].split(']')[0].split(', ')) <= {'propext','Classical.choice','Quot.sound'}
    assert r['swaps']=='0'
    final[m]={k:r[k] for k in ['attempt','source_revision','source_sha256','deps_fingerprint','exit','wall','peak_rss_kib','swaps','axioms']}
source_changed=subprocess.check_output(['git','diff','5676c09df','--name-only','--','crates'],cwd=ROOT,text=True).splitlines()
assert not source_changed,source_changed
result=dict(route_name='D99_P6_records_owned_reference',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    external_trust=['Kani/CBMC soundness under D90 harness assumptions','Charon/Aeneas source translation and the pinned backend models'],
    not_lean_axioms=True,field_coverage=coverage,solver_receipts=receipts,kernel_refinements=final,
    scope='All 20 owned-reference fields, named P6 record equality, and substitution through all four complete bank outputs of BuilderBankExtracted with BuilderStdModels. Does not prove Parts/copyCellMerged equivalence or successful compiler admission.',
    unchanged_shipped_crates=True)
(HERE/'builder-cont6-p6-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: six retained Kani verdicts, all 20 fields,',sum(len(v['axioms']) for v in final.values()),'kernel audits; no shipped crate changes')

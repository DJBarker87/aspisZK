"""No prover: check classifier conservativeness against every retained diagnostic."""
from NEH_scan import *
checks=[]
for p in sorted(E.glob('NEH_K*.rs')):
 receipt=p.with_suffix('')/'receipt.json'
 if not receipt.exists():continue
 t=p.read_text();r=json.loads(receipt.read_text());log=(receipt.parent/'stdout.log').read_text();c=classify({p.name:t})
 false_pass='VERIFICATION:- SUCCESSFUL' in log
 if false_pass:assert c['classification']=='AFFECTED',p
 checks.append(dict(source=p.name,sha256=sha(p.read_bytes()),classification=c['classification'],observed_false_pass=false_pass,exit=r['exit_status']))
assert classify({'x':'custom_static_macro!();'})['classification']=='AFFECTED'
assert classify({'x':'#[unknown_attr] fn f(){}'})['classification']=='AFFECTED'
assert classify({'x':'#[derive(Custom)] struct R;'})['classification']=='AFFECTED'
assert classify({'x':'macro_rules! m {()=>{}}'})['classification']=='AFFECTED'
assert classify({'x':'fn f(){}'},['unresolved_stub.rs'])['classification']=='AFFECTED'
assert classify({})['classification']=='AFFECTED'
assert classify({'x':'fn f(r:&mut usize){*r=1;}'})['classification']=='UNAFFECTED'
(E/'NEH_CLASSIFIER_TESTS.json').write_text(json.dumps(dict(status='PASS',scope='Finite diagnostics plus unresolved/macro/local boundary cases; not proof of completeness of a Rust compiler',checks=checks),indent=2)+'\n')
print(len(checks),'diagnostics checked')

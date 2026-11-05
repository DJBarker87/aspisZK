from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());s=inputs[C+'NGM_verifier.rs']
# (ad): control and call associations do not interpret proof bytes or weight words.
# Remove the eager 632+256 validity assumptions, proving a broader control domain.
for text in ['canonical_message(&bytes[..224],7);','canonical_message(&bytes[256..480],7);','canonical_message(&bytes[480..],64);']:
 assert s.count(text)==1;s=s.replace(text,'')
assert 'let weight_values:[K;64]=core::array::from_fn(|_|anyk());'in s
s=s.replace('let weight_values:[K;64]=core::array::from_fn(|_|anyk());','let weight_values:[K;64]=core::array::from_fn(|_|q(kani::any()));')
inputs[C+'NGM_verifier.rs']=s
(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n');pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins[C+'NGM_verifier.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else'/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
p=E/'NGM_CALLER_DOMAIN_REPAIR.json';x=json.loads(p.read_text());x.update(timed_out='K083 eager whole-input validity constraints;90 seconds;no credit',replacement='(ad) data-independent control separated from validity: all2528 bytes unconstrained, all64 raw QM31 weights arbitrary; no eager message/weight validation loops. SAME source-body/capture assertions and corruption controls. A pass on the broader raw inputs covers canonical inputs without a new validity premise.',pending='K084..099 eight positive/negative pairs');p.write_text(json.dumps(x,indent=2)+'\n')
with (E/'NGM_FINDINGS.md').open('a')as f:f.write('\nF5: K083 full eager-validity control shape timed out at90seconds,4.55GiB RSS,swap0. No credit/no unchanged retry. Replacement splits data-independent control from validation under(ad), removes632 message-word and256 weight canonical inequalities, keeps arbitrary full message/weights and exact source-body assertions. Stronger control domain; validity remains in separate caller/callee domain obligations.\n')
s=(E/'NGM_queue5.py').read_text().replace('for group in range(14):','for group in range(8):').replace('55+2*group','84+2*group').replace("f'verifier::NGM_dot::finish_g{group:02}'","f'verifier::NGM_verifier::finish_control_{group}'")
(E/'NGM_queue7.py').write_text(s)

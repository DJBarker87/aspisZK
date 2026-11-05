from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';name='crates/aspis-core/src/state_only_prefix.rs'
s=subprocess.check_output(['git','show',F+':'+name],text=True)
start=s.index('fn state_only_statement_points(');end=s.index('\nfn encode_statement_points',start);body=s[start:end].strip()
expected='''fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    for coordinate in (0..z.len()).rev() {
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut absorption = *z;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*z, successor, absorption]
}'''
assert body==expected
h=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text())['crates/aspis-core/src/NGW_points.rs']
step=h[h.index('fn step('):h.index('\nfn exercise')]
actual=step[step.index('let bit ='):step.rindex('}')].strip()
expected_step='''let bit = z[coordinate];
 let bit_and_carry = product(bit,*carry,log);
 successor[coordinate] = bit.add(*carry).sub(bit_and_carry.add(bit_and_carry));
 *carry = bit_and_carry;'''
assert actual==expected_step
mutations=[expected_step.replace('bit,*carry','*carry,bit'),expected_step.replace('bit_and_carry.add(bit_and_carry)','bit_and_carry'),expected_step.replace('*carry = bit_and_carry','*carry = bit'),expected_step.replace('successor[coordinate]','successor[0]')]
assert all(m!=actual for m in mutations)
out=dict(frozen_revision=F,source_sha256=hashlib.sha256(s.encode()).hexdigest(),function_body_sha256=hashlib.sha256(body.encode()).hexdigest(),native_step_sha256=hashlib.sha256(actual.encode()).hexdigest(),source_order=['read z[coordinate]','product(bit,carry)','add(bit,carry)','add(product,product)','sub(sum,twice)','write successor[coordinate]','carry=product'],transformation=['QM31::mul replaced by local-record arbitrary canonical reply (y); paired law required','carry passed as local mutable reference','single loop iteration, arbitrary canonical prestate; source loop retained separately'],assertions=dict(exact_frozen_body=True,exact_native_fission_step=True,mutation_controls_rejected=len(mutations)),claim='SOURCE TEXT ASSOCIATION ONLY; native controls and Lean induction required')
(E/'NGW_ERASURE.json').write_text(json.dumps(out,indent=2)+'\n')
print('source-ordered fission and four mutation controls checked')

"""Value-only structural binding for the frozen base-field inverse cut."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d371'
def compact(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
def body(s,marker):
 a=s.index(marker);a=s.index('{',a);b=a+1;depth=1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
s=(R/'crates/aspis-core/src/field.rs').read_text();ct=(R/'crates/aspis-core/src/field/ct.rs').read_text()
inv=body(s,'pub fn inv(self) -> M31')
expected='''#[cfg(feature = "r0-op-count")]
let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::FInv);
assert!(self.0 != 0, "inverse of zero");
let t2 = self.mul(self).mul(self);
let t4 = square_n(t2, 2).mul(t2);
let t8 = square_n(t4, 4).mul(t4);
let t16 = square_n(t8, 8).mul(t8);
let t24 = square_n(t16, 8).mul(t8);
let t28 = square_n(t24, 4).mul(t4);
let t29 = t28.mul(t28).mul(self);
let t30 = t29.mul(t29);
t30.mul(t30).mul(self)'''
assert compact(inv)==compact(expected)
assert compact(body(s,'fn square_n('))==compact('for _ in 0..count {value=value.mul(value);}value')
assert compact(body(s,'pub fn mul(self, rhs: M31)'))==compact('''#[cfg(feature="r0-op-count")]let _count=crate::r0_op_count::enter(crate::r0_op_count::Op::FMul);M31(reduce_u64(self.0 as u64 * rhs.0 as u64))''')
assert '#[cfg(feature = "ct-host-prover")]' in s
assert 'fn reduce_u64(x: u64) -> u32 { ct::reduce64(x) }' in s
assert compact(body(ct,'pub fn reduce64('))==compact('let x=(x&P as u64)+(x>>31);let x=(x&P as u64)+(x>>31);subtract_p(x as u32)')
receipt=E/'inverse-probe3/receipt.json';r=json.loads(receipt.read_text());assert r['exit']==0
log=(E/'inverse-probe3/out.log').read_text();assert 'same_input_native_inverse_modpow_comparisons=131 widened_product_comparisons=25 zero_inverse_expected_panic=true' in log
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'evidence_class':'structural (K-1 substitute), base inverse return/zero-boundary value cut',
 'native_field_sha256':hashlib.sha256(s.encode()).hexdigest(),'native_ct_sha256':hashlib.sha256(ct.encode()).hexdigest(),
 'exact_inverse_body_sha256':hashlib.sha256(inv.encode()).hexdigest(),
 'laws':['PV_L2C_NativeMultiply.decoded','PV_L2C_NativeReduce.reference','PV_L2C_InverseChain.exponent','PV_L2C_NativeInverse.square_decoded','PV_L2C_NativeInverse.zero','PV_L2C_InverseField.complete'],
 'native_differential':{'receipt':str(receipt.relative_to(R)),'sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'label':'finite same-input native inverse versus independent modular binary exponentiation (131), widened product versus integer remainder (25), caught expected zero panic'},
 'differences':['M31 erased to its raw word; decoded multiplication and canonical return proved on the exact width-64 reducer.',
 'square_n range loop becomes a remaining-count recursion; square_decoded proves all counts symbolically.',
 '38 multiplication chain remains in exact call order; exponent theorem evaluates only its scalar exponents.',
 'Native raw-zero assertion is Result.fail panic in Lean; it is never changed to a successful inverse at zero.',
 'r0-op-count instrumentation is not enabled by the selected ct-host-prover release; no observation-equivalence claim for that alternate feature is made.'],
 'remaining':'QM31/CM31 norm nonzero linkage to the honest helper NoPole domain and complete helper caller association; this leaf does not remove V357.'}
(E/'inverse-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked exact base inverse chain, zero assertion, square loop, widened multiply and ct reducer; linked finite native differential')

from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod mask_horner50 {
use super::{field::{QM31 as K,M31},prepared50};
pub fn go(q:[K;27],prepared:[[M31;3];3],left:u8,acc:K)->K {
 if left==0 {acc} else {
  let n=left-1;let value=prepared50::mul(prepared,acc).add(q[usize::from(n)]);
  go(q,prepared,n,value)
 }
}
pub fn eval(q:[K;27],x:K)->K {
 let prepared=prepared50::prepare(x);go(q,prepared,26,q[26])
}
}
''';p.write_text(s)
s=(E/'harness/extract-linears.py').read_text().replace('crate::linear50','crate::mask_horner50').replace('charon-v12','charon-v13').replace('aeneas-v12','aeneas-v13').replace('linears-v12','mask-horner-v13');(E/'harness/extract-mask-horner.py').write_text(s)
s=(E/'harness/bind-linears.py').read_text().replace('linears-v12','mask-horner-v13').replace('Linear50.lean','MaskHorner50.lean').replace('linears-callee-binding','mask-horner-callee-binding').replace('"linear50.go" in new and "linear50.power26" in new','"mask_horner50.go" in new and "mask_horner50.eval" in new');(E/'harness/bind-mask-horner.py').write_text(s)

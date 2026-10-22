from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod linear50 {
use super::field::{QM31 as K,M31};
pub fn go(point:[K;10],left:u8,suffix:K,weighted:K)->(K,K) {
 if left==0 {(suffix,weighted)} else {
  let n=left-1;let next=suffix.add(point[usize::from(n)]);
  let weighted=if n==0 {weighted} else {weighted.add(next)};
  go(point,n,next,weighted)
 }
}
pub fn eval(point:[K;10])->(K,K) {
 let (suffix,weighted)=go(point,10,K::ZERO,K::ZERO);
 (suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
  suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))))
}
pub fn power26(x:K)->K {
 let x2=x.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();
 x16.mul(x8).mul(x2)
}
}
''';p.write_text(s)
s=(E/'harness/extract-mle.py').read_text().replace('crate::mle50','crate::linear50').replace('charon-v11','charon-v12').replace('aeneas-v11','aeneas-v12').replace('mle-v11','linears-v12');(E/'harness/extract-linears.py').write_text(s)
s=(E/'harness/bind-mle.py').read_text().replace('mle-v11','linears-v12').replace('Mle50.lean','Linear50.lean').replace('mle-callee-binding','linears-callee-binding').replace('"mle50.mle" in new and "mle50.count" in new','"linear50.go" in new and "linear50.power26" in new');(E/'harness/bind-linears.py').write_text(s)

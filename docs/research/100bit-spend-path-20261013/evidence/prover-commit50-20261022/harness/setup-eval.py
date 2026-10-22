from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod eval50 {
use super::{field::{QM31 as K,M31},run50,prepared50};
pub fn block(p:[K;28],powers:[K;3],j:usize)->K {
 let start=j.wrapping_mul(4);
 p[start].add(run50::run(powers,[p[start.wrapping_add(1)],p[start.wrapping_add(2)],p[start.wrapping_add(3)]]))
}
pub fn go(p:[K;28],powers:[K;3],prepared:[[M31;3];3],left:u8,acc:K)->K {
 if left==0 {acc} else {
  let n=left-1;
  let product=prepared50::mul(prepared,acc);
  let value=block(p,powers,usize::from(n));
  go(p,powers,prepared,n,product.add(value))
 }
}
pub fn eval(p:[K;28],x:K)->K {
 let x2=x.square();let x3=x.mul(x2);let x4=x2.square();let powers=[x,x2,x3];
 let prepared=prepared50::prepare(x4);let acc=block(p,powers,6);
 go(p,powers,prepared,6,acc)
}
}
''';p.write_text(s)
s=(E/'harness/extract-prepared.py').read_text().replace('crate::prepared50','crate::eval50').replace('charon-v4','charon-v5').replace('aeneas-v4','aeneas-v5');(E/'harness/extract-eval.py').write_text(s)
s=(E/'harness/bind-prepared.py').read_text().replace('Prepared50.lean','Eval50.lean').replace('prepared-callee-binding','eval-callee-binding').replace('["Dot50", "Totals50", "Reconstruction49"]','["Dot50", "Totals50", "Reconstruction49", "Prepared50", "Run50"]')
s=s.replace('import AspisR1ProducerRelease47.Dot50','import AspisR1ProducerRelease47.Prepared50\nimport AspisR1ProducerRelease47.Run50\nimport AspisR1ProducerRelease47.Dot50');(E/'harness/bind-eval.py').write_text(s)

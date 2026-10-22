from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod prepared50 {
use super::field::{M31,CM31 as C,QM31 as K};
pub fn prepare(x:K)->[[M31;3];3] {
 let a=super::dot50::prepare_c(x.c0);
 let b=super::dot50::prepare_c(x.c1);
 let c=super::dot50::prepare_c(x.c0.add(x.c1));
 [a,b,c]
}
pub fn cm(left:[M31;3],right:C)->C {
 let m0=left[0].mul(right.a);let m1=left[1].mul(right.b);
 let m2=left[2].mul(right.a.add(right.b));
 C{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
pub fn combine(m0:C,m1:C,m2:C)->K {
 K{c0:m0.add(super::reconstruction::mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
pub fn mul(left:[[M31;3];3],right:K)->K {
 let m0=cm(left[0],right.c0);let m1=cm(left[1],right.c1);
 let m2=cm(left[2],right.c0.add(right.c1));
 combine(m0,m1,m2)
}
}
''';p.write_text(s)
s=(E/'harness/extract-run.py').read_text().replace('crate::run50','crate::prepared50').replace('charon-v3','charon-v4').replace('aeneas-v3','aeneas-v4');(E/'harness/extract-prepared.py').write_text(s)
s=(E/'harness/bind-run.py').read_text().replace('Run50.lean','Prepared50.lean').replace('run-callee-binding','prepared-callee-binding');(E/'harness/bind-prepared.py').write_text(s)

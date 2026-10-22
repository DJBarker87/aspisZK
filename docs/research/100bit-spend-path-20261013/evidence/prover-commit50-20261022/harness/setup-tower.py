from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod tower50 {
use super::field::{QM31 as K,CM31 as C};
pub fn cm_i(x:C)->C {C{a:x.b.neg(),b:x.a}}
pub fn mul(x:K,coordinate:u8)->K {
 match coordinate {
 0=>x,
 1=>K{c0:cm_i(x.c0),c1:cm_i(x.c1)},
 2=>K{c0:super::reconstruction::mul_r(x.c1),c1:x.c0},
 3=>K{c0:cm_i(super::reconstruction::mul_r(x.c1)),c1:cm_i(x.c0)},
 _=>panic!("tower coordinate out of range")
 }
}
}
''';p.write_text(s)
s=(E/'harness/extract-mask-horner.py').read_text().replace('crate::mask_horner50','crate::tower50').replace('charon-v13','charon-v14').replace('aeneas-v13','aeneas-v14').replace('mask-horner-v13','tower-v14');(E/'harness/extract-tower.py').write_text(s)
s=(E/'harness/bind-mask-horner.py').read_text().replace('mask-horner-v13','tower-v14').replace('MaskHorner50.lean','Tower50.lean').replace('mask-horner-callee-binding','tower-callee-binding').replace('"mask_horner50.go" in new and "mask_horner50.eval" in new','"tower50.cm_i" in new and "tower50.mul" in new');(E/'harness/bind-tower.py').write_text(s)

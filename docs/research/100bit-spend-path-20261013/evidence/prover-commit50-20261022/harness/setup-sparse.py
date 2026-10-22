from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod sparse50 {
use super::field::QM31 as K;
pub fn weight(point:[K;10],prefix:usize,width:u8,i:usize,left:u8,acc:K)->K {
 if left==0 {acc} else {
  let shift=usize::from(width).wrapping_sub(1).wrapping_sub(i);
  let bit=prefix.wrapping_shr(shift as u32)&1;
  let factor=if bit==0 {K::ONE.sub(point[i])} else {point[i]};
  weight(point,prefix,width,i.wrapping_add(1),left-1,acc.mul(factor))
 }
}
pub fn row(prefix:usize,trailing:u8,suffix:usize)->usize {
 prefix.wrapping_shl(u32::from(trailing))|suffix
}
}
''';p.write_text(s)
s=(E/'harness/extract-eval.py').read_text().replace('crate::eval50','crate::sparse50').replace('charon-v5','charon-v6').replace('aeneas-v5','aeneas-v6');(E/'harness/extract-sparse.py').write_text(s)
s=(E/'harness/bind-eval.py').read_text().replace('Eval50.lean','Sparse50.lean').replace('eval-callee-binding','sparse-callee-binding');(E/'harness/bind-sparse.py').write_text(s)

from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod sparse_sum50 {
use super::{field::QM31 as K,sparse50};
pub fn sum(point:[K;10],column:[K;1024],width:u8,trailing:u8,suffix:usize,pref:usize,left:u16,acc:K)->K {
 if left==0 {acc} else {
  let weight=sparse50::weight(point,pref,width,0,width,K::ONE);
  let row=sparse50::row(pref,trailing,suffix);
  let value=column[row];let product=weight.mul(value);
  sum(point,column,width,trailing,suffix,pref.wrapping_add(1),left-1,acc.add(product))
 }
}
}
''';p.write_text(s)
s=(E/'harness/extract-sparse.py').read_text().replace('crate::sparse50','crate::sparse_sum50').replace('charon-v7','charon-v8').replace('aeneas-v7','aeneas-v8').replace('str(R/\'extraction/dot-owner\')','str(R/\'extraction/sparse-sum-v8\')');(E/'harness/extract-sparse-sum.py').write_text(s)
s=(E/'harness/bind-sparse.py').read_text().replace("source=E/'extraction/dot-owner/","source=E/'extraction/sparse-sum-v8/").replace('Sparse50.lean','SparseSum50.lean').replace('sparse-callee-binding','sparse-sum-callee-binding');s=s.replace('"sparse50.weight" in new and "sparse50.row" in new','"sparse_sum50.sum" in new');s=s.replace('"Kernels49"]','"Kernels49", "Sparse50"]').replace('import AspisR1ProducerRelease47.Kernels49','import AspisR1ProducerRelease47.Sparse50\nimport AspisR1ProducerRelease47.Kernels49');(E/'harness/bind-sparse-sum.py').write_text(s)

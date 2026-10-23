from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod sparse_scan50 {
use super::field::QM31 as K;
pub fn one(x:K)->bool {
 x.c0.a.0==1 && x.c0.b.0==0 && x.c1.a.0==0 && x.c1.b.0==0
}
pub fn boolean(x:K)->bool {
 x.c0.b.0==0 && x.c1.a.0==0 && x.c1.b.0==0 && (x.c0.a.0==0 || x.c0.a.0==1)
}
pub fn width(point:[K;10],left:u8)->u8 {
 if left==0 {0} else {
  let n=left-1;let value=point[usize::from(n)];
  if boolean(value) {width(point,n)} else {left}
 }
}
pub fn suffix(point:[K;10],start:usize,left:u8)->usize {
 if left==0 {0} else {
  let n=left-1;
  let prev=suffix(point,start,n);
  let value=point[start.wrapping_add(usize::from(n))];
  prev.wrapping_shl(1)|usize::from(one(value))
 }
}
}
''';p.write_text(s)
s=(E/'harness/extract-sparse-sum.py').read_text().replace('crate::sparse_sum50','crate::sparse_scan50').replace('charon-v9','charon-v10').replace('aeneas-v9','aeneas-v10').replace('sparse-sum-v9','sparse-scan-v10');(E/'harness/extract-scan.py').write_text(s)
s=(E/'harness/bind-sparse-sum.py').read_text().replace('sparse-sum-v9','sparse-scan-v10').replace('SparseSum50.lean','SparseScan50.lean').replace('sparse-sum-callee-binding','sparse-scan-callee-binding').replace('"sparse_sum50.sum" in new','"sparse_scan50.width" in new and "sparse_scan50.suffix" in new');(E/'harness/bind-scan.py').write_text(s)

from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod mle50 {
use super::{field::QM31 as K,sparse_scan50,sparse_sum50};
pub fn count(width:u8)->u16 {1u16.wrapping_shl(u32::from(width))}
pub fn mle(point:[K;10],column:[K;1024])->K {
 let width=sparse_scan50::width(point,10);let trailing=10-width;
 let suffix=sparse_scan50::suffix(point,usize::from(width),trailing);
 sparse_sum50::sum(point,column,width,trailing,suffix,0,count(width),K::ZERO)
}
}
''';p.write_text(s)
s=(E/'harness/extract-scan.py').read_text().replace('crate::sparse_scan50','crate::mle50').replace('charon-v10','charon-v11').replace('aeneas-v10','aeneas-v11').replace('sparse-scan-v10','mle-v11');(E/'harness/extract-mle.py').write_text(s)
s=(E/'harness/bind-scan.py').read_text().replace('sparse-scan-v10','mle-v11').replace('SparseScan50.lean','Mle50.lean').replace('sparse-scan-callee-binding','mle-callee-binding').replace('"sparse_scan50.width" in new and "sparse_scan50.suffix" in new','"mle50.mle" in new and "mle50.count" in new').replace('"Kernels49", "Sparse50"]','"Kernels49", "Sparse50", "SparseScan50", "SparseSum50"]');s=s.replace('import AspisR1ProducerRelease47.Sparse50','import AspisR1ProducerRelease47.SparseScan50\nimport AspisR1ProducerRelease47.SparseSum50\nimport AspisR1ProducerRelease47.Sparse50');(E/'harness/bind-mle.py').write_text(s)

from pathlib import Path
E=Path(__file__).resolve().parent.parent;p=E/'dot-owner/lib.rs';s=p.read_text();s+='''
pub mod mask_finish50 {
use super::{field::QM31 as K,linear50};
pub fn eval(shared:K,explicit_linear:K,g:K)->K {
 shared.add(K::ONE.add(linear50::power26(explicit_linear)).mul(g))
}
}
''';p.write_text(s)
s=(E/'harness/extract-tower.py').read_text().replace('crate::tower50','crate::mask_finish50').replace('charon-v15','charon-v16').replace('aeneas-v15','aeneas-v16').replace('tower-v15','mask-finish-v16');(E/'harness/extract-mask-finish.py').write_text(s)
s=(E/'harness/bind-tower.py').read_text().replace('tower-v15','mask-finish-v16').replace('Tower50.lean','MaskFinish50.lean').replace('tower-callee-binding','mask-finish-callee-binding').replace('"tower50.cm_i" in new and "tower50.mul" in new','"mask_finish50.eval" in new').replace('"SparseScan50", "SparseSum50"]','"SparseScan50", "SparseSum50", "Linear50"]');s=s.replace('import AspisR1ProducerRelease47.SparseScan50','import AspisR1ProducerRelease47.Linear50\nimport AspisR1ProducerRelease47.SparseScan50');(E/'harness/bind-mask-finish.py').write_text(s)

from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'stored-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'factor-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'factor-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-stored-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
pub mod stored {
use super::field::QM31 as K;
pub fn product(rows:[[K;4];5],j:usize,d:usize,left:u8,acc:K)->K {
 if left==0 {acc} else {
  let digit=(j>>((2*d) as u32))&3;
  let next=acc.mul(rows[d][digit]);product(rows,j,d+1,left-1,next)
 }
}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','stored-owner').replace('WeightOwner','StoredOwner').replace('crate::owned','crate::stored');(E/'harness/extract-stored.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','stored-owner').replace('KernelOwner','StoredOwner').replace('Kernels49.lean','Stored49.lean').replace('kernels-callee-binding','stored-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.Basis');(E/'harness/bind-stored.py').write_text(s)

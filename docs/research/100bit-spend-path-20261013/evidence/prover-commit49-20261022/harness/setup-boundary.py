from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent
D=E/'boundary-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'sample-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'sample-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-boundary-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
pub mod owned {
use super::field::M31;
pub fn sum(q:[u32;28],i:usize,left:u8,total:u64)->u64 {
 if left==0 {total} else {
  let next=total+u64::from(q[i]);
  sum(q,i+1,left-1,next)
 }
}
pub fn limb(q:[u32;28])->M31 {
 let initial=2*u64::from(q[0]);
 M31::reduce_u64(sum(q,1,27,initial))
}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','boundary-owner').replace('WeightOwner','BoundaryOwner')
(E/'harness/extract-boundary.py').write_text(s)

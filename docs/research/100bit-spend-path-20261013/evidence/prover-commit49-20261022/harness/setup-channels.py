from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'channel-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'sample-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'sample-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-channel-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
pub mod channels {
use super::field::M31;
pub fn sum(a:[M31;3],b:[M31;3],i:usize,left:u8,total:u64)->u64 {
 if left==0 {total} else {
  let product=u64::from(a[i].0).wrapping_mul(u64::from(b[i].0));
  let next=total.wrapping_add(product);sum(a,b,i+1,left-1,next)
 }
}
pub fn dot3(a:[M31;3],b:[M31;3])->M31 {M31::reduce_u64(sum(a,b,0,3,0))}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','channel-owner').replace('WeightOwner','ChannelOwner').replace('crate::owned','crate::channels');(E/'harness/extract-channels.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','channel-owner').replace('KernelOwner','ChannelOwner').replace('Kernels49.lean','Channels49.lean').replace('kernels-callee-binding','channels-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.Funs');(E/'harness/bind-channels.py').write_text(s)

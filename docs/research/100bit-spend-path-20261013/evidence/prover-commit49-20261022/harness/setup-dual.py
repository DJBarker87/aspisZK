from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'dual-owner';D.mkdir(exist_ok=True)
P=E.parent/'prover-commit48-20261022/batched-owner'
shutil.copytree(P/'field',D/'field',dirs_exist_ok=True);shutil.copy(P/'field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-dual-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text((P/'lib.rs').read_text()+'''
pub mod dual {
use super::{field::WideExact as E,dual_cell};
pub fn first(q:[E;1024],a:E,mut out:[E;256],i:usize,left:u16)->[E;256] {
 if left==0 {out} else {
  let h=[q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]];
  out[i]=dual_cell(h,a);first(q,a,out,i+1,left-1)
 }
}
pub fn all(q:[E;1024],a:E)->[E;256] {first(q,a,[E::ZERO;256],0,256)}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','dual-owner').replace('WeightOwner','DualOwner').replace('crate::owned','crate::dual');(E/'harness/extract-dual.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','dual-owner').replace('KernelOwner','DualOwner').replace('Kernels49.lean','Dual49.lean').replace('kernels-callee-binding','dual-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.Batched48');s=s.replace('reuse=[]','old.update(declarations(L/"AspisR1ProducerRelease47/Batched48.lean"))\nold.update(declarations(L/"AspisR1ProducerRelease47/Pairs.lean"))\nreuse=[]');(E/'harness/bind-dual.py').write_text(s)

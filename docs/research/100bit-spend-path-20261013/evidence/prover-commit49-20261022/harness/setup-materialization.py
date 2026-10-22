from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'materialization-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'weight-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'weight-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-materialization-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text((E/'weight-owner/lib.rs').read_text()+'''
pub mod materialization {
use super::{field::{QM31 as K,WideExact as E},owned::cell};
pub fn fill(kp:[E;7],raw:[[K;7];1024],mut out:[E;1024],j:usize,left:u16)->[E;1024] {
 if left==0 {out} else {
  out[j]=cell(kp,raw[j],0,7,out[j]);fill(kp,raw,out,j+1,left-1)
 }
}
pub fn all(kp:[E;7],raw:[[K;7];1024])->[E;1024] {fill(kp,raw,[E::ZERO;1024],0,1024)}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','materialization-owner').replace('WeightOwner','MaterializationOwner').replace('crate::owned','crate::materialization');(E/'harness/extract-materialization.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','materialization-owner').replace('KernelOwner','MaterializationOwner').replace('Kernels49.lean','Materialization49.lean').replace('kernels-callee-binding','materialization-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.Weights49');s=s.replace('reuse=[]','old.update(declarations(L/"AspisR1ProducerRelease47/Weights49.lean"))\nreuse=[]');(E/'harness/bind-materialization.py').write_text(s)

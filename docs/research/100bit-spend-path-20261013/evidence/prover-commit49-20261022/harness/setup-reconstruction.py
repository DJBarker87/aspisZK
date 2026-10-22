from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'reconstruction-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'sample-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'sample-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-reconstruction-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
pub mod reconstruction {
use super::field::{QM31 as K,CM31 as C,M31};
pub fn cm(s:[u64;3])->C {
 let m0=M31::reduce_u64(s[0]);let m1=M31::reduce_u64(s[1]);let m2=M31::reduce_u64(s[2]);
 C{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
pub fn mul_r(x:C)->C {
 let two_a=x.a.double();let real=two_a.sub(x.b);
 let two_b=x.b.double();let imag=x.a.add(two_b);
 C{a:real,b:imag}
}
pub fn q(s:[[u64;3];3])->K {
 let m0=cm(s[0]);let m1=cm(s[1]);let m2=cm(s[2]);
 K{c0:m0.add(mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','reconstruction-owner').replace('WeightOwner','ReconstructionOwner').replace('crate::owned','crate::reconstruction');(E/'harness/extract-reconstruction.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','reconstruction-owner').replace('KernelOwner','ReconstructionOwner').replace('Kernels49.lean','Reconstruction49.lean').replace('kernels-callee-binding','reconstruction-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.Funs');(E/'harness/bind-reconstruction.py').write_text(s)

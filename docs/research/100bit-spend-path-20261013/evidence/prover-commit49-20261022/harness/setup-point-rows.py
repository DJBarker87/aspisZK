from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'point-rows-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'factor-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'factor-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-point-rows-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text((E/'factor-owner/lib.rs').read_text()+'''
pub mod point_rows {
use super::{field::QM31 as K,factors::point};
pub const TAU:[usize;5]=[3,4,2,0,1];
pub fn fill(p:[K;10],mut out:[[K;4];5],d:usize,left:u8)->[[K;4];5] {
 if left==0 {out} else {
 let t=TAU[d];let a=p[9-2*t];let b=p[8-2*t];
 out[d]=point(a,b);fill(p,out,d+1,left-1)
 }
}
pub fn all(p:[K;10])->[[K;4];5] {fill(p,[[K::ZERO;4];5],0,5)}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','point-rows-owner').replace('WeightOwner','PointRowsOwner').replace('crate::owned','crate::point_rows');(E/'harness/extract-point-rows.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','point-rows-owner').replace('KernelOwner','PointRowsOwner').replace('Kernels49.lean','PointRows49.lean').replace('kernels-callee-binding','point-rows-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.CircleFactors49');s=s.replace('reuse=[]','old.update(declarations(L/"AspisR1ProducerRelease47/Factors49.lean"))\nold.update(declarations(L/"AspisR1ProducerRelease47/CircleFactors49.lean"))\nreuse=[]');(E/'harness/bind-point-rows.py').write_text(s)

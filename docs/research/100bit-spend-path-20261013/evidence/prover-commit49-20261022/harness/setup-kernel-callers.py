from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'kernel-callers-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'kernel-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'kernel-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-kernel-callers-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text((E/'kernel-owner/lib.rs').read_text()+'''
pub mod extras {
use super::{field::{QM31 as K,CM31 as C,M31},inverse_ref,kernels::power};
pub fn half()->K {K::from_cm31(C::from_m31(inverse_ref(M31(2))))}
pub fn libra(extra:[K;2],j:usize)->K {
 if j<56 {power(extra[j/28],(j%28) as u8,K::ONE)} else {K::ZERO}
}
}
''')
s=(E/'harness/extract-kernels.py').read_text().replace('kernel-owner','kernel-callers-owner').replace('KernelOwner','KernelCallersOwner').replace('kernel-owner49','kernel-callers-owner49').replace('crate::kernels','crate::extras').replace('-v2','-v1');(E/'harness/extract-kernel-callers.py').write_text(s)
s=(E/'harness/bind-kernels.py').read_text().replace('kernel-owner','kernel-callers-owner').replace('KernelOwner','KernelCallersOwner').replace('Kernels49.lean','KernelCallers49.lean').replace('kernels-callee-binding','kernel-callers-callee-binding').replace('import AspisR1ProducerRelease47.Interpolate48','import AspisR1ProducerRelease47.Kernels49');s=s.replace('reuse=[]','old.update(declarations(L/"AspisR1ProducerRelease47/Kernels49.lean"))\nold.update(declarations(L/"AspisR1ProducerRelease47/Samples49.lean"))\nreuse=[]');(E/'harness/bind-kernel-callers.py').write_text(s)

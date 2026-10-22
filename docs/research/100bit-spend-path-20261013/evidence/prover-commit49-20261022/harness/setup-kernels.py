from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'kernel-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'sample-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'sample-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-kernel-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
old=(E.parent/'prover-commit48-20261022/interpolate-owner/lib.rs').read_text();start=old.index('pub fn square_ref');end=old.index('pub fn scalar_ref',start)
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
use field::M31;
'''+old[start:end]+'''
pub mod kernels {
use super::{field::{QM31 as K,CM31 as C},inverse_ref};
pub fn square(x:K)->K {x.square()}
pub fn power(base:K,exp:u8,acc:K)->K {
 if exp==0 {acc} else {
  let next=if exp&1!=0 {acc.mul(base)} else {acc};
  power(base.square(),exp>>1u32,next)
 }
}
pub fn inverse_c(x:C)->C {
 let norm=x.a.mul(x.a).add(x.b.mul(x.b));
 let inv_norm=inverse_ref(norm);
 C{a:x.a.mul(inv_norm),b:x.b.neg().mul(inv_norm)}
}
pub fn mul_r(x:C)->C {
 let two_a=x.a.double();let real=two_a.sub(x.b);
 let two_b=x.b.double();let imag=x.a.add(two_b);
 C{a:real,b:imag}
}
pub fn inverse_q(x:K)->Option<K> {
 if x.is_zero() {None} else {
  let norm=x.c0.square().sub(mul_r(x.c1.square()));
  let ni=inverse_c(norm);
  Some(K{c0:x.c0.mul(ni),c1:x.c1.neg().mul(ni)})
 }
}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','kernel-owner').replace('WeightOwner','KernelOwner').replace('crate::owned','crate::kernels').replace('owner-charon-v1','owner-charon-v2').replace('owner-aeneas-v1','owner-aeneas-v2');(E/'harness/extract-kernels.py').write_text(s)

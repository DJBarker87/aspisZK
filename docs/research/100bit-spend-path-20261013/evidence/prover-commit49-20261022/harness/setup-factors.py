from pathlib import Path
import shutil
E=Path(__file__).resolve().parent.parent;D=E/'factor-owner';D.mkdir(exist_ok=True)
shutil.copytree(E/'sample-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(E/'sample-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-factor-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
pub mod factors {
use super::field::QM31 as K;
pub fn point(a:K,b:K)->[K;4] {
 [K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)]
}
pub fn circle(x:K,y:K)->[K;4] { [K::ONE,y,x,x.mul(y)] }
pub fn double(x:K)->K {x.mul(x).add(x.mul(x)).sub(K::ONE)}
pub fn product(q:[K;5],i:usize,left:u8,s:K)->K {
 if left==0 {s} else {
  let next=s.mul(q[i]);
  product(q,i+1,left-1,next)
 }
}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','factor-owner').replace('WeightOwner','FactorOwner').replace('crate::owned','crate::factors');(E/'harness/extract-factors.py').write_text(s)

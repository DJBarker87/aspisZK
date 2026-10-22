from pathlib import Path
import shutil
E=Path('docs/research/100bit-spend-path-20261013/evidence/prover-commit49-20261022');P=E.parent/'prover-commit48-20261022'
D=E/'weight-owner';D.mkdir(exist_ok=True)
shutil.copytree(P/'extra-owner/field',D/'field',dirs_exist_ok=True);shutil.copy(P/'extra-owner/field.rs',D/'field.rs')
(D/'Cargo.toml').write_text('[package]\nname="simulator-weight-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''#![allow(unexpected_cfgs)]
pub mod field;
pub mod owned {
use super::field::{QM31 as K,WideExact as E};
pub fn cell(kp:[E;7],raw:[K;7],kind:usize,left:u8,sum:E)->E {
 if left==0 {sum} else {
  let next=sum.add(kp[kind].mul_qm31(raw[kind]));
  cell(kp,raw,kind+1,left-1,next)
 }
}
pub fn inactive(q:[E;1024],raw:[K;1024],j:usize,left:u16,sum:E)->E {
 if left==0 {sum} else {
  let next=sum.add(q[j].mul_qm31(raw[j]));
  inactive(q,raw,j+1,left-1,next)
 }
}
}
''')
s=(E/'harness/extract-samples.py').read_text().replace('sample-owner','weight-owner').replace('SampleOwner','WeightOwner').replace('charon-v3','charon-v1').replace('aeneas-v3','aeneas-v1')
(E/'harness/extract-weights.py').write_text(s)

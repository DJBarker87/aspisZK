from pathlib import Path
import shutil,subprocess
B=Path('docs/research/100bit-spend-path-20261013/evidence');O=B/'prover-commit49-20261022';E=B/'prover-commit50-20261022'
for d in ['pins','lean','endpoint','extraction','native-receipts','native-snapshots']: (E/d).mkdir(exist_ok=True)
for f in ['lean.py','collect.py','capped.py','kani.py','extract-reconstruction.py','bind-reconstruction.py']:
 s=(O/'harness'/f).read_text().replace('commit49','commit50').replace('10000<=int(attempt)<=10199','10200<=int(attempt)<=10299')
 (E/'harness'/f).write_text(s)
(E/'pins/revision.txt').write_text(subprocess.check_output(['git','rev-parse','HEAD'],text=True))
for f in ['before.lean.txt','after.lean.txt']: shutil.copy(O/'endpoint'/f,E/'endpoint'/f)
D=E/'dot-owner';shutil.copytree(O/'reconstruction-owner',D,dirs_exist_ok=True)
(D/'Cargo.toml').write_text('[package]\nname="simulator-dot-owner50"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
s=(D/'lib.rs').read_text();s=s[:s.index('pub mod reconstruction')]+'''pub mod dot50 {
use super::field::{QM31 as K,CM31 as C,M31};
pub fn prepare_c(x:C)->[M31;3] {[x.a,x.b,x.a.add(x.b)]}
pub fn prepare(x:K)->[[M31;3];3] {
 let z=x.c0.add(x.c1);
 [prepare_c(x.c0),prepare_c(x.c1),prepare_c(z)]
}
}
'''
(D/'lib.rs').write_text(s)
s=(E/'harness/extract-reconstruction.py').read_text().replace('reconstruction-owner','dot-owner').replace('ReconstructionOwner49','DotOwner50').replace('crate::reconstruction','crate::dot50')
(E/'harness/extract-dot.py').write_text(s)
s=(E/'harness/bind-reconstruction.py').read_text().replace('reconstruction-owner','dot-owner').replace('ReconstructionOwner49','DotOwner50').replace('Reconstruction49.lean','Dot50.lean').replace('reconstruction-callee-binding','dot-callee-binding')
(E/'harness/bind-dot.py').write_text(s)

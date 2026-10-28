"""Optimized finite source/copy gate; restore the scratch test byte-for-byte."""
from pathlib import Path
import subprocess,hashlib,json,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');S=H/'candidate/src';D=H/'batch2c-d188-full-v2';D.mkdir(exist_ok=False)
p=S/'crates/aspis-r1-cost-probe/src/host_weights.rs';original=p.read_bytes()
test=r'''
#[cfg(test)]
mod pv_b2_full_checks {
 extern crate std;
 use super::*;
 use aspis_core::field::{CM31,M31,P};
 #[test]
 fn full_mutation_outputs() {
  for variant in [Variant::S1,Variant::S2,Variant::D] {
   let a=Weights{variant,factors:[[[K::ONE;4];5];5],points:[[K::ONE;10];3],extra:[K::ONE;2]};
   let b=crate::weights::Weights{variant,factors:a.factors,points:a.points,extra:a.extra};
   let mut out=[E::ZERO;1024];a.materialize(E::ONE,&mut out).unwrap();
   assert_eq!(out.as_slice(),b.materialize(E::ONE).unwrap().as_slice());
   let selected=out.map(|x|x.to_limbs());
   std::println!("PV_B2_NATIVE_FULL_OK_{:?}={:?}",variant,selected);
  }
 }
}
'''
(D/'scratch-tests.rs.txt').write_text(test)
cmd=['cargo','test','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--features','optimized-terminal,r1p-check,ct-host-prover','--lib','--','pv_b2_full_checks','--test-threads=1','--nocapture']
(D/'command.json').write_text(json.dumps(dict(command=cmd,source_revision=(H/'candidate/source-revision.txt').read_text().strip(),source_sha256=hashlib.sha256(original).hexdigest(),expected_time='optimized Rust test compilation followed by complete 1024-element mutation Result comparison; no elimination'),indent=2)+'\n')
try:
 p.write_bytes(original+test.encode())
 r=subprocess.run(cmd,cwd=S)
finally:
 p.write_bytes(original)
 (D/'restored.json').write_text(json.dumps(dict(restored=p.read_bytes()==original,sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2)+'\n')
raise SystemExit(r.returncode)

from pathlib import Path
import subprocess
R=Path('crates/aspis-r1-cost-probe/src')
def prior(p):return subprocess.check_output(['git','show','codex/pv-route2-20261027:evidence/pv-route2-20261027/dropfree/native/'+p],text=True)
s=prior('op249.rs').replace('use aspis_core::field::{M31,CM31,QM31,WideExact,P};','//! Prover-local Drop-free samplers (D187 batch 2).\nuse aspis_core::field::{WideExact,P};')
(R/'host_sampler.rs').write_text(s)
s=prior('op252.rs');a=s.index('fn double');s='''//! Prover-local fixed-storage weights (D187 batch 2).
use aspis_core::field::{QM31,QM31 as K,WideExact as E};
use aspis_core::circle::SecureCirclePoint;
use crate::{transport::Variant,verifier::Error};
pub use crate::weights::{QUARTER,PERM};
pub struct Weights {pub variant:Variant,pub factors:[[[K;4];5];5],pub points:[[K;10];3],pub extra:[K;2]}
'''+s[a:]
s=s.replace('pub fn weights_new(', 'impl Weights {\n#[inline(never)]\npub fn new(').rstrip()
orig=(R/'weights.rs').read_text();raw=orig[orig.index('    pub fn raw('):orig.index('    fn scalar_factor')]
raw=raw.replace('(0..10).fold(K::ONE,|v,b|v.mul(if r&(1<<b)==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]}))','{ let mut v=K::ONE; let mut b=0usize; while b<10 { v=v.mul(if r&(1usize<<(b as u32))==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]}); b+=1; } v }').replace('(0..5).fold(K::ONE,|v,d|v.mul(self.factors[k][d][(j>>(2*d))&3]))','{ let mut v=K::ONE; let mut d=0usize; while d<5 { v=v.mul(self.factors[k][d][(j>>((2*d) as u32))&3]); d+=1; } v }')
s+='\n'+raw+'''
    /// The caller owns allocation and retains Error::Allocation before this kernel.
    pub fn materialize(&self,kappa:E,w:&mut [E;1024])->Result<(),Error> {
        let kp=powers::<7>(kappa);
        let mut j=0usize;
        while j<1024 {
            let mut v=E::ZERO;
            let mut kind=0usize;
            while kind<7 { v=v.add(kp[kind].mul_qm31(self.raw(kind,j))); kind+=1; }
            w[j]=v; j+=1;
        }
        Ok(())
    }
}
'''
a=orig.index('pub fn powers');b=orig.index('pub fn kpowers');s+='\n'+orig[a:b]
(R/'host_weights.rs').write_text(s)
p=R/'lib.rs';p.write_text(p.read_text()+'\n#[cfg(feature="prover")] mod host_sampler;\n#[cfg(feature="prover")] mod host_weights;\n')
for name in ['prover.rs','sim.rs']:
 p=R/name;s=p.read_text().replace('weights::{Weights,QUARTER,PERM}','host_weights::{Weights,QUARTER,PERM}').replace('weights::Weights','host_weights::Weights').replace('crate::weights::powers','crate::host_weights::powers')
 call='kappa' if name=='prover.rs' else 'd.kappa'
 s=s.replace('let weights=w.materialize('+call+')?;', '''let mut weights=match aspis_core::r0::heap::filled(1024,E::ZERO) { Ok(v)=>v, Err(_)=>return Err(Error::Allocation) };
    w.materialize('''+call+''',weights.as_mut_slice().try_into().unwrap())?;''')
 p.write_text(s)
p=R/'host_transcript.rs';p.write_text(p.read_text().replace('crate::sampler::gamma_sample','crate::host_sampler::gamma_sample').replace('crate::sampler::ordinary_sample','crate::host_sampler::ordinary_sample'))
p=R/'dense.rs';p.write_text(p.read_text().replace('sample::gamma_sample','crate::host_sampler::gamma_sample').replace('sample::ordinary_sample','crate::host_sampler::ordinary_sample'))

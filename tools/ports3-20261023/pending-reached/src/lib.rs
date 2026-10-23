#![allow(dead_code,unexpected_cfgs)]
use aspis_core::field::{M31,CM31,QM31 as K};
use aspis_r1_cost_probe::verifier::Error;
struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
impl BatchedWeights {
    fn new(weights:&[K])->Result<Self,Error> {
        let mut raw=aspis_core::r0::heap::filled(weights.len(),[0u64;4]).map_err(|_|Error::Allocation)?;
        let mut index=0;
        while index<weights.len() {
            let w=weights[index];
            raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
            index+=1;
        }
        Ok(Self{raw,terms:0})
    }
}
#[cfg(kani)] mod proofs {
use super::*;
fn any_k()->K {let x:[u32;4]=kani::any();K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
#[kani::proof]
#[kani::unwind(66)]
fn pending64_success_contents() {
 let weights:[K;64]=core::array::from_fn(|_|any_k());
 let n=64;
 let out=BatchedWeights::new(&weights[..n]);
 if let Ok(b)=out {
   assert_eq!(b.terms,0);assert_eq!(b.raw.len(),n);
   let j:usize=kani::any();
   if j<n {let q=weights[j];assert_eq!(b.raw[j][0],q.c0.a.0 as u64);assert_eq!(b.raw[j][1],q.c0.b.0 as u64);assert_eq!(b.raw[j][2],q.c1.a.0 as u64);assert_eq!(b.raw[j][3],q.c1.b.0 as u64);}
 }
}
}

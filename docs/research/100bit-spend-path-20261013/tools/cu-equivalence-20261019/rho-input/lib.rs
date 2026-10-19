extern crate alloc;
extern crate self as aspis_core;
pub mod field {
/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
/// CM31 = M31[i] / (i^2 + 1). Element a + b*i.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
/// QM31 = CM31[u] / (u^2 - (2 + i)). Element c0 + c1*u. (stwo parameterization)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
#[inline(always)]
fn reduce_u64(x: u64) -> u32 {
    // reference_canonical: two mask/shift folds bring any u64 to at most
    // P+3, then one conditional subtract canonicalizes. Supporting the full
    // u64 range lets four maximal M31 products be accumulated before one
    // reduction: 4*(P-1)^2 < 2^64.
    let x = (x & P as u64) + (x >> 31u32);
    let x = (x & P as u64) + (x >> 31u32);
    let x = x as u32;
    if x >= P {
        x - P
    } else {
        x
    }
}
impl M31 {
    /// Canonically reduce any `u64`. This is used by four-term lazy dot
    /// products whose accumulator may exceed 2^62 but cannot overflow u64.
    #[inline(always)]
    pub fn reduce_u64(value: u64) -> M31 {
        M31(reduce_u64(value))
    }
}
}
pub mod r0 { pub mod heap { use alloc::vec::Vec;
pub fn filled<T:Copy>(_:usize,_:T)->Result<Vec<T>,()> {unreachable!()}
}}
pub mod verifier { use alloc::vec::Vec; use crate::field::{QM31 as K,M31};
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
/// Transaction-local residues. At a group boundary each limb is <2^34.
/// Four products add at most 4*(P-1)^2; adding the retained folded residue
/// still fits u64 because 4*(P-1)^2+2^34 < 2^64. Flush after each four queries.
struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
impl BatchedWeights {
    fn new(weights:&[K])->Result<Self,Error> {
        let mut raw=aspis_core::r0::heap::filled(weights.len(),[0u64;4]).map_err(|_|Error::Allocation)?;
        for (out,w) in raw.iter_mut().zip(weights) {
            *out=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
        }
        Ok(Self{raw,terms:0})
    }
    #[inline(always)]
    fn push(&mut self,index:usize,power:K,basis:M31) {
        let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
        for j in 0..4 {self.raw[index][j]+=u64::from(limbs[j])*u64::from(basis.0);}
        if self.terms&3==3 {
            for limb in &mut self.raw[index] {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
        }
    }
    fn value(&self,index:usize)->K {
        let [a,b,c,d]=self.raw[index].map(M31::reduce_u64);
        K{c0:aspis_core::field::CM31{a,b},c1:aspis_core::field::CM31{a:c,b:d}}
    }
    fn finish(&self,weights:&mut[K]) {for (i,w) in weights.iter_mut().enumerate(){*w=self.value(i);}}
}
}

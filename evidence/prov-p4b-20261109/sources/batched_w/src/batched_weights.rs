//! Source-exact verifier batching operations; only the wrapper is added.
use alloc::vec::Vec;
use crate::aspis_core;
use crate::aspis_core::field::{QM31 as K, M31};

struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
impl BatchedWeights {
    #[inline(always)]
    fn push(&mut self,index:usize,power:K,basis:M31) {
        let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
        for j in 0..4 {self.raw[index][j]+=u64::from(limbs[j])*u64::from(basis.0);}
        if self.terms&3==3 {
            let lane=self.raw[index];
            self.raw[index]=[
                (lane[0]&0x7fff_ffff)+(lane[0]>>31),
                (lane[1]&0x7fff_ffff)+(lane[1]>>31),
                (lane[2]&0x7fff_ffff)+(lane[2]>>31),
                (lane[3]&0x7fff_ffff)+(lane[3]>>31),
            ];
        }
    }
    fn value(&self,index:usize)->K {
        let lane=self.raw[index];
        let [a,b,c,d]=[
            M31::reduce_u64(lane[0]),
            M31::reduce_u64(lane[1]),
            M31::reduce_u64(lane[2]),
            M31::reduce_u64(lane[3]),
        ];
        K{c0:aspis_core::field::CM31{a,b},c1:aspis_core::field::CM31{a:c,b:d}}
    }
}

/// Execute exactly the source push body over caller-provided raw lanes. The
/// wrapper exposes post-state and omits `new` allocation and verifier context.
pub fn push_entry(raw:Vec<[u64;4]>, terms:usize, index:usize, power:K, basis:M31) -> (Vec<[u64;4]>,usize) {
    let mut weights=BatchedWeights { raw, terms };
    weights.push(index,power,basis);
    (weights.raw,weights.terms)
}

/// Execute exactly the source value body on caller-provided raw lanes.
pub fn value_entry(raw:Vec<[u64;4]>, terms:usize, index:usize) -> K {
    let weights=BatchedWeights { raw, terms };
    weights.value(index)
}

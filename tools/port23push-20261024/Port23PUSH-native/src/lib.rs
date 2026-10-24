#![allow(non_snake_case, unexpected_cfgs, private_interfaces)]
extern crate alloc;
pub mod field;
pub mod verifier {
    use super::field::{QM31 as K, M31};
    use alloc::vec::Vec;
    include!("carrier.rs");
    impl BatchedWeights {
    #[inline(always)]
    fn push(&mut self,index:usize,power:K,basis:M31) {
        let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush);
    }
    }
    include!("update.rs");
    pub fn Port23PUSH_push(b: &mut BatchedWeights,index:usize,power:K,basis:M31) {
        b.push(index,power,basis)
    }
}

use std::vec::Vec;
pub mod field {
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
pub struct M31(pub u32);
impl M31 {
 pub const ZERO:Self=Self(0);
 pub fn mul(self,_:M31)->M31 {unreachable!()}
 pub fn inv(self)->M31 {unreachable!()}
}
}
use field::M31;
pub fn backward(flat:&Vec<M31>,prefixes:&Vec<M31>,product:M31)->Vec<M31> {
        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }

flat_inverse
}

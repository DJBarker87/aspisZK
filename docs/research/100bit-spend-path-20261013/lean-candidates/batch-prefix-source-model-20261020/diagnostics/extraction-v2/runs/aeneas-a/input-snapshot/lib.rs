use std::vec::Vec;
pub mod field {
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
pub struct M31(pub u32);
impl M31 {
 pub const ONE:Self=Self(1);
 pub fn mul(self,_:M31)->M31 {unreachable!()}
}
}
use field::M31;
pub fn prefix_product(flat:Vec<M31>)->(Vec<M31>,Vec<M31>,M31) {
        let mut prefixes=Vec::with_capacity(flat.len());
        let mut product=M31::ONE;
        for &value in &flat {prefixes.push(product);product=product.mul(value);}

(flat,prefixes,product)
}

use std::vec::Vec;
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
pub struct M31(pub u32);
pub fn geometry_groups(flat_inverse:&Vec<M31>,line_z_values:&Vec<M31>)->Vec<[M31;5]> {
(0..line_z_values.len()).map(|i|core::array::from_fn(|j|flat_inverse[5*i+j])).collect()
}
pub fn option_context_anchor(v:Option<u8>)->Option<u8>{v}

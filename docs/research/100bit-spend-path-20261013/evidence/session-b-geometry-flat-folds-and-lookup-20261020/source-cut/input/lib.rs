use std::vec::Vec;
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
pub struct M31(pub u32);
struct QueryGeometry { start:usize, inverses:Vec<[M31;5]>, line_z:Vec<M31> }
impl QueryGeometry {
    #[inline(always)]
    fn for_query(&self,index:usize)->&[M31;5] {&self.inverses[index-self.start]}
}
pub fn for_query_entry(self_:&QueryGeometry,index:usize)->[M31;5] { *self_.for_query(index) }
pub fn option_context_anchor(v:Option<u8>)->Option<u8>{v}

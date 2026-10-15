//! UNPROVED COST PROBE. S uses the D18 digit permutation; D uses retained D13.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Variant { S1, S2, D }
pub const TAU: [usize; 5] = [3, 4, 2, 0, 1];
impl Variant {
    pub fn tag(self) -> u8 { match self { Self::S1=>1,Self::S2=>2,Self::D=>3 } }
    pub fn from_tag(tag:u8) -> Option<Self> { match tag {1=>Some(Self::S1),2=>Some(Self::S2),3=>Some(Self::D),_=>None} }
    pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }
    pub fn final_len(self) -> usize { 1024 >> (2*self.folds()) }
    pub fn row(self, j:usize) -> usize {
        if self == Self::D { return aspis_core::r0::transport::COEFFICIENT_TO_ROW[j] as usize; }
        let mut out=0;
        for d in 0..5 { out |= ((j>>(2*d))&3) << (2*TAU[d]); }
        out
    }
    pub fn coefficients<T:Copy>(self, rows: &[T;1024]) -> [T;1024] {
        core::array::from_fn(|j|rows[self.row(j)])
    }
    pub fn rows<T:Copy>(self, coefficients: &[T;1024]) -> [T;1024] {
        let mut out=*coefficients;
        for j in 0..1024 { out[self.row(j)]=coefficients[j]; }
        out
    }
}

pub mod field {
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
impl M31 {
pub const ZERO:Self=Self(0);pub const ONE:Self=Self(1);
pub fn mul(self,_rhs:Self)->Self{unreachable!()}
pub fn add(self,_rhs:Self)->Self{unreachable!()}
pub fn sub(self,_rhs:Self)->Self{unreachable!()}
    #[inline(always)]
    pub fn double(self) -> M31 {
        self.add(self)
    }
}
}
use field::M31;
pub fn basis(length:usize,mut node:M31)->[M31;256] {
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<length {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    basis
}

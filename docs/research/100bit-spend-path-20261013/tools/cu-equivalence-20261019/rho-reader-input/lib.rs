pub mod field {
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
impl QM31 {pub fn from_le_bytes(_bytes:&[u8])->Option<Self>{unreachable!()}}
}
pub mod verifier {use crate::field::QM31 as K;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
struct Reader<'a>{bytes:&'a[u8],at:usize}
impl<'a> Reader<'a> {
    fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
    fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}
}

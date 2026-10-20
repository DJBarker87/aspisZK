pub struct VecProjection<B> {pub buf:B,pub len:usize}
pub trait RawReserve {
    type ReserveError;
    fn try_reserve_exact(&mut self,len:usize,additional:usize)->Result<(),Self::ReserveError>;
}
pub fn source_reserve<B:RawReserve>(value:&mut VecProjection<B>,additional:usize)->Result<(),B::ReserveError> {
        value.buf.try_reserve_exact(value.len, additional)
}

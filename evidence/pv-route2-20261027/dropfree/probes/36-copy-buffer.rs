// Measurement: Copy elements and caller-owned fixed-capacity carrier; generic Vec<T> row remains open.
#[derive(Clone,Copy)] pub struct Buffer<T:Copy,const CAP:usize>{pub data:[T;CAP],pub len:usize}
pub fn array_try_from<T:Copy,const N:usize,const CAP:usize>(v:Buffer<T,CAP>,fill:T)->Result<[T;N],Buffer<T,CAP>>{
 if v.len!=N {return Err(v);}let mut out=[fill;N];let mut i=0usize;while i<N {out[i]=v.data[i];i+=1;}Ok(out)
}

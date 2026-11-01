//! Owned safe value reference. Only the cfg(kani) parent includes this file.
pub fn take<T: Default>(x: T) -> (T,T) { (x,T::default()) }
pub fn borrow_bytes(x: &[u8]) -> &[u8] { x }
pub fn pop<T>(x: &[T]) -> (Option<&T>,&[T]) {
    if x.is_empty() { return (None,x); }
    (x.last(),&x[..x.len()-1])
}
pub fn empty<T>(x:&[T])->bool { x.len()==0 }
pub fn default_vec<T>()->Vec<T> { Vec::new() }
pub fn array<T,const N:usize>(x:Vec<T>)->Result<[T;N],Vec<T>> {
    if x.len()!=N { return Err(x); }
    let mut it=x.into_iter();
    Ok(std::array::from_fn(|_| it.next().unwrap()))
}
/// Unix source algorithm: absolute suffix replaces; otherwise insert one separator
/// exactly when the retained prefix is nonempty and does not end in '/'.
pub fn join(base:&[u8],suffix:&[u8])->Vec<u8> {
    if suffix.first()==Some(&b'/') {return suffix.to_vec();}
    let mut out=base.to_vec();
    if !out.is_empty() && out.last()!=Some(&b'/') {out.push(b'/');}
    out.extend_from_slice(suffix);out
}

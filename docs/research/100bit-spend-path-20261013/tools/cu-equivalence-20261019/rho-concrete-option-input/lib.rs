extern crate alloc;
use alloc::vec::Vec;
/// Transaction-local residues. At a group boundary each limb is <2^34.
/// Four products add at most 4*(P-1)^2; adding the retained folded residue
/// still fits u64 because 4*(P-1)^2+2^34 < 2^64. Flush after each four queries.
struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
pub fn as_mut<T>(value:&mut Option<T>)->Option<&mut T> {
    match *value { Some(ref mut x) => Some(x), None => None }
}
pub fn map<T,U,F>(value:Option<T>,f:F)->Option<U> where F:FnOnce(T)->U {
    match value { Some(x) => Some(f(x)), None => None }
}
pub fn deref_mut<'a,'b,T>(value:&'a mut &'b mut T)->&'a mut T { value }
pub fn as_deref_mut<'a,'b,T>(value:&'a mut Option<&'b mut T>)->Option<&'a mut T> {
    map(as_mut(value),deref_mut)
}

pub fn concrete_reborrow<'a,'b>(value:&'a mut Option<&'b mut BatchedWeights>)->Option<&'a mut BatchedWeights> {
    as_deref_mut(value)
}

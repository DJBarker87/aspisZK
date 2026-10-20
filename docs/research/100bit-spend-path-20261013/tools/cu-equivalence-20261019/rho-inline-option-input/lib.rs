#[inline(always)]
pub fn as_mut<T>(value:&mut Option<T>)->Option<&mut T> {
    match *value { Some(ref mut x) => Some(x), None => None }
}
#[inline(always)]
pub fn map<T,U,F>(value:Option<T>,f:F)->Option<U> where F:FnOnce(T)->U {
    match value { Some(x) => Some(f(x)), None => None }
}
#[inline(always)]
pub fn deref_mut<'a,'b,T>(value:&'a mut &'b mut T)->&'a mut T { value }
#[inline(always)]
pub fn as_deref_mut<'a,'b,T>(value:&'a mut Option<&'b mut T>)->Option<&'a mut T> {
    map(as_mut(value),deref_mut)
}

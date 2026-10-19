// Branch-normalized form of the std as_mut/map/deref_mut composition.
// Equivalence to that source composition is a separate checked obligation.
pub fn reborrow<'a,'b,T>(value:&'a mut Option<&'b mut T>)->Option<&'a mut T> {
    match value { Some(x) => Some(&mut **x), None => None }
}

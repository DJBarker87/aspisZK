pub fn clear_ref() {}
pub struct Plan<P>{pub preparation:P,pub seed:[u8;32],pub encoded_marker:[u8;208]}
pub fn preparation_ref<P>(x:Plan<P>)->P{x.preparation}

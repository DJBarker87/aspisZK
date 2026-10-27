// Full generic owned-Vec measurement. Complete Err(Vec<T>) ownership is retained.
// This baseline deliberately keeps the destructor semantics; it is not called Drop-free.
pub fn array_try_from<T,const N:usize>(v:Vec<T>)->Result<[T;N],Vec<T>> {
    v.try_into()
}

// Exact shipped generic conversion entry; no alternative conversion body.
pub fn array_from_vec<T,const N:usize>(v:Vec<T>)->Result<[T;N],Vec<T>> {v.try_into()}

#[cfg(kani)] mod empty_gate {
    static mut DROPS:usize=0;
    struct Token;
    impl Drop for Token {fn drop(&mut self) {unsafe{DROPS+=1;}}}
    // Only empty Vecs: no element allocation, copy or clone is performed.
    // This gate covers the length branch and empty Drop ownership only.
    #[kani::proof]
    #[kani::unwind(3)]
    fn empty_noncopy_length_branches() {
        let v:Vec<Token>=Vec::new();
        match super::array_from_vec::<Token,1>(v) {
            Err(v)=>{assert_eq!(v.len(),0);assert_eq!(v.capacity(),usize::MAX);},
            Ok(_)=>panic!("wrong-length conversion succeeded")
        }
        let v:Vec<Token>=Vec::new();
        match super::array_from_vec::<Token,0>(v) {
            Ok(a)=>assert_eq!(a.len(),0),
            Err(_)=>panic!("zero-length conversion failed")
        }
        assert_eq!(unsafe{DROPS},0);
    }
}

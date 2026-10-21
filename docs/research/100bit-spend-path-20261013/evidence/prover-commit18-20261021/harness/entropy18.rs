// Checks the actual shipped generator. Only the OS boundary is stubbed.
// No assertion below treats OS errors as impossible or proves an OS law.
#[cfg(kani)]
mod entropy18 {
    use super::*;
    static mut CALLS:usize=0;
    static mut RAW:[u8;96]=[0;96];
    fn draw(dest:&mut [u8])->Result<(),getrandom::Error> {
        assert_eq!(dest.len(),96);
        unsafe {CALLS+=1;dest.copy_from_slice(&RAW);}
        Ok(())
    }
    fn failed_draw(dest:&mut [u8])->Result<(),getrandom::Error> {
        assert_eq!(dest.len(),96);
        unsafe {CALLS+=1;}
        Err(getrandom::Error::UNSUPPORTED)
    }
    #[kani::proof]
    #[kani::unwind(98)]
    #[kani::stub(getrandom::fill,draw)]
    fn first_success() {
        let raw:[u8;96]=kani::any();
        kani::assume(raw[..32]!=[0;32]);
        kani::assume(raw[32..64]!=[0;32]);
        kani::assume(raw[64..]!=[0;32]);
        unsafe {RAW=raw;CALLS=0;}
        let actual=StateOnlyAttemptSecrets::generate().unwrap();
        assert_eq!(actual.mask_nonce,raw[..32]);
        assert_eq!(*actual.field_mask_entropy,raw[32..64]);
        assert_eq!(*actual.leaf_salt_seed,raw[64..]);
        assert_eq!(unsafe{CALLS},1);
    }
    #[kani::proof]
    #[kani::unwind(98)]
    #[kani::stub(getrandom::fill,failed_draw)]
    fn os_failure() {
        unsafe {CALLS=0;}
        let actual=StateOnlyAttemptSecrets::generate();
        assert!(matches!(actual,Err(StateOnlyAttemptEntropyError::Os(_))));
        assert_eq!(unsafe{CALLS},1);
    }
    #[kani::proof]
    #[kani::unwind(98)]
    #[kani::stub(getrandom::fill,draw)]
    fn zero_exhaustion() {
        unsafe {RAW=[0;96];CALLS=0;}
        let actual=StateOnlyAttemptSecrets::generate();
        assert!(matches!(actual,Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
        assert_eq!(unsafe{CALLS},16);
    }
}

#[cfg(kani)]
pub mod reference;
#[cfg(all(kani,not(pv_cb_extract)))]
mod checks {
    use super::reference;
    use std::os::unix::ffi::OsStrExt;
    #[kani::proof]
    fn take_u64() {
        let x:u64=kani::any();let mut actual=x;
        let old=std::mem::take(&mut actual);
        assert_eq!((old,actual),reference::take(x));
    }
    #[derive(Debug,PartialEq,Eq)]
    struct Nonzero(u64);
    impl Default for Nonzero {fn default()->Self {Self(37)}}
    #[kani::proof]
    fn take_nonzero() {
        let x:u64=kani::any();let mut actual=Nonzero(x);
        let old=std::mem::take(&mut actual);
        assert_eq!((old,actual),reference::take(Nonzero(x)));
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn pathbuf_borrow16() {
        let bytes:[u8;16]=kani::any();let len:usize=kani::any();kani::assume(len<=16);
        let owned=std::path::PathBuf::from(std::ffi::OsStr::from_bytes(&bytes[..len]));
        let deref:&std::path::Path=std::ops::Deref::deref(&owned);
        let asref:&std::path::Path=owned.as_ref();
        assert_eq!(deref.as_os_str().as_bytes(),reference::borrow_bytes(&bytes[..len]));
        assert_eq!(asref.as_os_str().as_bytes(),reference::borrow_bytes(&bytes[..len]));
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn string_path16() {
        let bytes:[u8;16]=kani::any();let len:usize=kani::any();kani::assume(len<=16);
        if let Ok(s)=std::str::from_utf8(&bytes[..len]) {
            let owned=s.to_string();let path:&std::path::Path=owned.as_ref();
            assert_eq!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
        }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn path_join8() {
        let a:[u8;8]=kani::any();let b:[u8;8]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=8 && m<=8);
        let base=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let suffix=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let actual=base.join(suffix);let expected=reference::join(&a[..n],&b[..m]);
        assert_eq!(actual.as_os_str().as_bytes(),expected.as_slice());
    }
}

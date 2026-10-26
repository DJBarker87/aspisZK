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
    #[kani::proof]
    #[kani::unwind(18)]
    fn pop16() {
        let bytes:[u64;16]=kani::any(); let len:usize=kani::any(); kani::assume(len<=16);
        let mut actual=bytes[..len].to_vec(); let old=actual.pop();
        let (expected,tail)=reference::pop(&bytes[..len]);
        assert_eq!(old,expected.copied()); assert_eq!(actual.as_slice(),tail);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn empty16() {
        let bytes:[u64;16]=kani::any(); let len:usize=kani::any(); kani::assume(len<=16);
        let actual=bytes[..len].to_vec();
        assert_eq!(actual.is_empty(),reference::empty(&bytes[..len]));
    }
    #[kani::proof]
    fn default_vec() {
        let actual:Vec<u64>=Default::default();
        assert_eq!(actual,reference::default_vec::<u64>());
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn array4() {
        let bytes:[u64;16]=kani::any(); let len:usize=kani::any(); kani::assume(len<=16);
        let actual:Result<[u64;4],Vec<u64>>=bytes[..len].to_vec().try_into();
        let expected=reference::array::<u64,4>(bytes[..len].to_vec());
        assert_eq!(actual,expected);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn reserve_overflow() {
        let bytes:[u8;16]=kani::any(); let len:usize=kani::any(); kani::assume(len<=16);
        let mut actual=bytes[..len].to_vec();
        assert!(actual.try_reserve_exact(usize::MAX).is_err());
        assert_eq!(actual.as_slice(),&bytes[..len]);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn reserve_small() {
        let bytes:[u8;16]=kani::any(); let len:usize=kani::any(); let n:usize=kani::any();
        kani::assume(len<=16 && n<=16);
        let mut actual=bytes[..len].to_vec(); let result=actual.try_reserve_exact(n);
        if result.is_ok() { assert!(actual.capacity()>=len+n); }
        assert_eq!(actual.as_slice(),&bytes[..len]);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn push_ascii8() {
        let a:[u8;8]=kani::any();let b:[u8;8]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=8 && m<=8);
        for i in 0..8 {kani::assume(a[i]<128 && b[i]<128);}
        let mut actual=std::str::from_utf8(&a[..n]).unwrap().to_string();
        actual.push_str(std::str::from_utf8(&b[..m]).unwrap());
        let mut expected=a[..n].to_vec();expected.extend_from_slice(&b[..m]);
        assert_eq!(actual.as_bytes(),expected.as_slice());
    }
    #[kani::proof]
    fn capacity16() {
        let n:usize=kani::any();kani::assume(n<=16);
        let actual=String::with_capacity(n);
        assert!(actual.is_empty());assert!(actual.capacity()>=n);
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn string_ascii8() {
        let bytes:[u8;8]=kani::any();let len:usize=kani::any();kani::assume(len<=8);
        for i in 0..8 {kani::assume(bytes[i]<128);}
        let owned=std::str::from_utf8(&bytes[..len]).unwrap().to_string();
        let path:&std::path::Path=owned.as_ref();
        assert_eq!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn string_scalar() {
        let scalar:u32=kani::any();
        if let Some(c)=char::from_u32(scalar) {
            let owned=c.to_string(); let path:&std::path::Path=owned.as_ref();
            assert_eq!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
        }
    }
    #[kani::proof]
    fn reserve_zst_overflow() {
        let mut actual:Vec<()>=Vec::new();
        assert!(actual.try_reserve_exact(usize::MAX).is_ok());
        assert!(actual.is_empty());
    }
}

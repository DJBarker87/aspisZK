#![feature(allocator_api)]
extern crate alloc;
#[path="/home/dombarker/project-offloads/codex-pv-kstub-20261028/KMX_stubs.rs"] pub mod KMX_stubs;
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
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
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
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn path_join8_negative() {
        let a:[u8;8]=kani::any();let b:[u8;8]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=8 && m<=8);
        let base=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let suffix=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let actual=base.join(suffix);let expected=reference::join(&a[..n],&b[..m]);
        assert_ne!(actual.as_os_str().as_bytes(),expected.as_slice());
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn pop16() {
        let bytes:[u64;16]=kani::any(); let len:usize=kani::any(); kani::assume(len<=16);
        let mut actual=bytes[..len].to_vec(); let old=actual.pop();
        let (expected,tail)=reference::pop(&bytes[..len]);
        assert_eq!(old,expected.copied()); assert_eq!(actual.len(),tail.len());
        for i in 0..actual.len() {assert_eq!(actual[i],tail[i]);}
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
        let bytes:[u64;16]=kani::any(); let len:usize=kani::any(); kani::assume(len<=4);
        let actual:Result<[u64;4],Vec<u64>>=bytes[..len].to_vec().try_into();
        let expected=reference::array::<u64,4>(bytes[..len].to_vec());
        match (actual,expected) {
            (Ok(a),Ok(b))=>{for i in 0..4 {assert_eq!(a[i],b[i]);}},
            (Err(a),Err(b))=>{assert_eq!(a.len(),b.len());for i in 0..a.len() {assert_eq!(a[i],b[i]);}},
            _=>panic!("different result variants"),
        }
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
        let mut actual=String::with_capacity(n);let mut suffix=String::with_capacity(m);
        for i in 0..n {actual.push(a[i] as char);}
        for i in 0..m {suffix.push(b[i] as char);}
        actual.push_str(&suffix);
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
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn string_ascii8() {
        let bytes:[u8;8]=kani::any();let len:usize=kani::any();kani::assume(len<=8);
        for i in 0..8 {kani::assume(bytes[i]<128);}
        let owned=std::str::from_utf8(&bytes[..len]).unwrap().to_string();
        let path:&std::path::Path=owned.as_ref();
        assert_eq!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
    }
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn string_ascii8_negative() {
        let bytes:[u8;8]=[65;8];let len:usize=8;kani::assume(len<=8);
        for i in 0..8 {kani::assume(bytes[i]<128);}
        let owned=std::str::from_utf8(&bytes[..len]).unwrap().to_string();
        let path:&std::path::Path=owned.as_ref();
        assert_ne!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
    }
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn string_scalar() {
        let scalar:u32=kani::any();
        if let Some(c)=char::from_u32(scalar) {
            let owned=c.to_string(); let path:&std::path::Path=owned.as_ref();
            assert_eq!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
        }
    }
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn string_scalar_negative() {
        let scalar:u32=65;
        if let Some(c)=char::from_u32(scalar) {
            let owned=c.to_string(); let path:&std::path::Path=owned.as_ref();
            assert_ne!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
        }
    }
    #[kani::proof]
    fn reserve_zst_overflow() {
        let mut actual:Vec<()>=Vec::new();
        assert!(actual.try_reserve_exact(usize::MAX).is_ok());
        assert!(actual.is_empty());
    }
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn push_ascii1() {
        let a:u8=kani::any();let b:u8=kani::any();
        kani::assume(a<128 && b<128);
        let mut actual=String::new();actual.push(a as char);
        let mut suffix=String::new();suffix.push(b as char);actual.push_str(&suffix);
        assert_eq!(actual.as_bytes(),&[a,b]);
    }
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn push_ascii1_negative() {
        let a:u8=65;let b:u8=66;
        kani::assume(a<128 && b<128);
        let mut actual=String::new();actual.push(a as char);
        let mut suffix=String::new();suffix.push(b as char);actual.push_str(&suffix);
        assert_ne!(actual.as_bytes(),&[a,b]);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn take_array4() {
        let x:[u64;4]=kani::any();let mut actual=x;
        let old=std::mem::take(&mut actual);
        let (expected,cleared)=reference::take(x);
        for i in 0..4 {assert_eq!(old[i],expected[i]);assert_eq!(actual[i],cleared[i]);}
    }

}

#[cfg(kani)]
pub mod shipped {
 pub fn string_capacity(n:usize)->String {String::with_capacity(n)}
 pub fn vec_pop<T>(x:&mut Vec<T>)->Option<T> {x.pop()}
 pub fn vec_empty<T>(x:&Vec<T>)->bool {x.is_empty()}
 pub fn vec_default<T>()->Vec<T> {Default::default()}
 pub fn vec_array<T,const N:usize>(x:Vec<T>)->Result<[T;N],Vec<T>> {x.try_into()}
 pub fn path_deref(x:&std::path::PathBuf)->&std::path::Path {std::ops::Deref::deref(x)}
 pub fn take<T:Default>(x: &mut T)->T {std::mem::take(x)}
 pub fn path_join<P:AsRef<std::path::Path>>(x:&std::path::Path,p:P)->std::path::PathBuf {x.join(p)}
 pub fn string_push(mut x:String,y:&str)->String {x.push_str(y);x}
 pub fn reserve_exact<T>(mut x:Vec<T>,n:usize)->(Result<(),std::collections::TryReserveError>,Vec<T>) {let r=x.try_reserve_exact(n);(r,x)}

}

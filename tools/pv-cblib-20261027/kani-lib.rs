#![allow(dead_code)]
// Safe references are compiled with the real std/alloc implementation.
fn empty_reference<T>(v: &Vec<T>) -> bool { v.len() == 0 }
fn default_reference<T>() -> Vec<T> { Vec::new() }
fn pop_reference<T>(v: &mut Vec<T>) -> Option<T> {
    if v.len() == 0 { None } else { Some(v.remove(v.len() - 1)) }
}
#[cfg(kani)]
mod checks {
    use super::*;
    #[kani::proof]
    #[kani::unwind(10)]
    fn empty_u8() {
        let n: usize = kani::any(); kani::assume(n <= 8);
        let mut v = Vec::new();
        for _ in 0..n { v.push(kani::any::<u8>()); }
        assert_eq!(v.is_empty(), empty_reference(&v));
    }
    #[kani::proof]
    fn default_u8() {
        assert_eq!(Vec::<u8>::default(), default_reference::<u8>());
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn pop_u8() {
        let n: usize = kani::any(); kani::assume(n <= 8);
        let mut v = Vec::new();
        for _ in 0..n { v.push(kani::any::<u8>()); }
        let mut w = v.clone();
        assert_eq!(v.pop(), pop_reference(&mut w));
        assert_eq!(v,w);
    }
}

fn join_bytes_reference(base: &[u8], path: &[u8]) -> Vec<u8> {
    let mut out=Vec::new();
    let absolute=path.len()>0 && path[0]==b'/';
    if !absolute {
        let mut i=0;
        while i<base.len() { out.push(base[i]); i+=1; }
        if base.len()>0 && base[base.len()-1]!=b'/' { out.push(b'/'); }
    }
    let mut j=0;
    while j<path.len() { out.push(path[j]); j+=1; }
    out
}
#[cfg(kani)]
mod path_checks {
    use super::*;
    use std::os::unix::ffi::{OsStrExt,OsStringExt};
    fn bytes() -> Vec<u8> {
        let n:usize=kani::any(); kani::assume(n<=4);
        let mut v=Vec::new();
        for _ in 0..n {v.push(kani::any::<u8>());}
        v
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn path_borrows() {
        let b=bytes();
        let p=std::path::PathBuf::from(std::ffi::OsString::from_vec(b.clone()));
        let d:&std::path::Path=&p;
        let a:&std::path::Path=p.as_ref();
        assert_eq!(d.as_os_str().as_bytes(),b.as_slice());
        assert_eq!(a.as_os_str().as_bytes(),b.as_slice());
        let n:usize=kani::any();kani::assume(n<=2);
        let mut s=String::new();
        for _ in 0..n {s.push(kani::any::<char>());}
        let a:&std::path::Path=s.as_ref();
        assert_eq!(a.as_os_str().as_bytes(),s.as_bytes());
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn path_join() {
        let b=bytes();let q=bytes();
        let p=std::path::PathBuf::from(std::ffi::OsString::from_vec(b.clone()));
        let qpath=std::path::PathBuf::from(std::ffi::OsString::from_vec(q.clone()));
        let native=p.join(&qpath);
        let reference=join_bytes_reference(&b,&q);
        assert_eq!(native.as_os_str().as_bytes(),reference.as_slice());
    }
}

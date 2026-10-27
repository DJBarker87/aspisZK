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

fn path_owned_reference(p: std::path::PathBuf) -> std::path::PathBuf {p}

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
    fn pathbuf_borrows() {
        let p=std::path::PathBuf::from(std::ffi::OsString::from_vec(bytes()));
        let i:usize=kani::any();
        let (len,left,right)={
            let d:&std::path::Path=&p;
            let a:&std::path::Path=p.as_ref();
            (d.as_os_str().as_bytes().len(),
             d.as_os_str().as_bytes().get(i).copied(),
             a.as_os_str().as_bytes().get(i).copied())
        };
        let reference=path_owned_reference(p);
        let r=reference.as_os_str().as_bytes();
        assert_eq!(len,r.len());
        assert_eq!(left,r.get(i).copied());
        assert_eq!(right,r.get(i).copied());
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn path_join() {
        let p=std::path::PathBuf::from(std::ffi::OsString::from_vec(bytes()));
        let qpath=std::path::PathBuf::from(std::ffi::OsString::from_vec(bytes()));
        let native=p.join(&qpath);
        let reference=join_bytes_reference(p.as_os_str().as_bytes(),qpath.as_os_str().as_bytes());
        let i:usize=kani::any();
        assert_eq!(native.as_os_str().as_bytes().len(),reference.len());
        assert_eq!(native.as_os_str().as_bytes().get(i).copied(),reference.get(i).copied());
        // Same bounded byte inputs cover String->Path and append on valid UTF-8.
        if let (Ok(mut a),Ok(b))=(String::from_utf8(p.as_os_str().as_bytes().to_vec()),
                                  String::from_utf8(qpath.as_os_str().as_bytes().to_vec())) {
            let path:&std::path::Path=a.as_ref();
            assert_eq!(path.as_os_str().as_bytes().len(),a.as_bytes().len());
            assert_eq!(path.as_os_str().as_bytes().get(i),a.as_bytes().get(i));
            let before=a.as_bytes().to_vec();
            a.push_str(&b);
            assert_eq!(a.len(),before.len()+b.len());
            let expected=if i<before.len() {before.get(i).copied()}
                         else {b.as_bytes().get(i-before.len()).copied()};
            assert_eq!(a.as_bytes().get(i).copied(),expected);
            let capacity:usize=kani::any();kani::assume(capacity<=8);
            let empty=String::with_capacity(capacity);
            assert_eq!(empty.len(),0);
            assert!(empty.capacity()>=capacity);
        }
    }
}

// Resume: separate gates isolate pure views and allocation-free content laws.
#[cfg(kani)]
mod split_checks {
    use std::os::unix::ffi::OsStrExt;
    #[kani::proof]
    #[kani::unwind(4)]
    fn string_path() {
        let raw: [u8;2] = kani::any();
        if let Ok(s) = String::from_utf8(raw.to_vec()) {
            let path: &std::path::Path = s.as_ref();
            let i: usize = kani::any();
            assert_eq!(path.as_os_str().as_bytes().len(), s.as_bytes().len());
            assert_eq!(path.as_os_str().as_bytes().get(i), s.as_bytes().get(i));
        }
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn string_capacity() {
        let n: usize = kani::any(); kani::assume(n<=4);
        let s=String::with_capacity(n);
        assert_eq!(s.len(),0);
        assert!(s.capacity()>=n);
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn string_push() {
        let raw: [u8;2] = kani::any();
        if let Ok(mut s)=String::from_utf8(raw.to_vec()) {
            let tail: [u8;1]=kani::any();
            if let Ok(t)=std::str::from_utf8(&tail) {
                s.push_str(t);
                let i:usize=kani::any();
                assert_eq!(s.len(),3);
                let expected=if i<2 {raw.get(i).copied()} else {tail.get(i-2).copied()};
                assert_eq!(s.as_bytes().get(i).copied(),expected);
            }
        }
    }
}

#[cfg(kani)]
mod join_split {
    use super::*;
    use std::os::unix::ffi::OsStrExt;
    #[kani::proof]
    #[kani::unwind(6)]
    fn join_one_byte() {
        let a:[u8;1]=kani::any(); let b:[u8;1]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();
        kani::assume(n<=1 && m<=1);
        let p=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let q=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let native=p.join(q);
        let reference=join_bytes_reference(&a[..n],&b[..m]);
        let i:usize=kani::any();
        assert_eq!(native.as_os_str().as_bytes().len(),reference.len());
        assert_eq!(native.as_os_str().as_bytes().get(i),reference.get(i));
    }
}

#![feature(allocator_api)]
extern crate alloc;
#[path="/home/dombarker/project-offloads/codex-pv-kstub-20261028/KMX_stubs.rs"] pub mod KMX_stubs;

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
    #[kani::unwind(18)]
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
    #[kani::unwind(18)]
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
    #[kani::unwind(18)]
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
    #[kani::unwind(18)]
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
    #[kani::unwind(10)]
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
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
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn string_path_negative() {
        let raw: [u8;2] = [65;2];
        if let Ok(s) = String::from_utf8(raw.to_vec()) {
            let path: &std::path::Path = s.as_ref();
            let i: usize = 0;
            assert_eq!(path.as_os_str().as_bytes().len(), s.as_bytes().len());
            assert_ne!(path.as_os_str().as_bytes().get(i), s.as_bytes().get(i));
        }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn string_capacity() {
        let n: usize = kani::any(); kani::assume(n<=4);
        let s=String::with_capacity(n);
        assert_eq!(s.len(),0);
        assert!(s.capacity()>=n);
    }
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
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
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn string_push_negative() {
        let raw: [u8;2] = [65;2];
        if let Ok(mut s)=String::from_utf8(raw.to_vec()) {
            let tail: [u8;1]=[66;1];
            if let Ok(t)=std::str::from_utf8(&tail) {
                s.push_str(t);
                let i:usize=0;
                assert_eq!(s.len(),3);
                let expected=if i<2 {raw.get(i).copied()} else {tail.get(i-2).copied()};
                assert_ne!(s.as_bytes().get(i).copied(),expected);
            }
        }
    }
}

#[cfg(kani)]
mod join_split {
    use super::*;
    use std::os::unix::ffi::OsStrExt;
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
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
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn join_one_byte_negative() {
        let a:[u8;1]=[65;1]; let b:[u8;1]=[66;1];
        let n:usize=1;let m:usize=1;
        kani::assume(n<=1 && m<=1);
        let p=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let q=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let native=p.join(q);
        let reference=join_bytes_reference(&a[..n],&b[..m]);
        let i:usize=0;
        assert_eq!(native.as_os_str().as_bytes().len(),reference.len());
        assert_ne!(native.as_os_str().as_bytes().get(i),reference.get(i));
    }
}

#[cfg(kani)]
mod resume8 {
    #[kani::proof]
    #[kani::unwind(18)]
    fn capacity_bytes() {
        let n:usize=kani::any();kani::assume(n<=4);
        let native=String::with_capacity(n);
        let reference=Vec::<u8>::new();
        assert_eq!(native.as_bytes(),reference.as_slice());
        assert!(native.capacity()>=n);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn pop_u32() {
        let n:usize=kani::any();kani::assume(n<=2);
        let raw:[u32;2]=kani::any();
        let mut v=raw[..n].to_vec();let mut r=raw[..n].to_vec();
        let native=v.pop();
        let reference=if r.len()==0 {None} else {Some(r.remove(r.len()-1))};
        assert_eq!(native,reference);assert_eq!(v,r);
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn array_u32_two() {
        let raw:[u32;2]=kani::any();let v=raw.to_vec();
        let native:Result<[u32;2],Vec<u32>>=v.try_into();
        assert_eq!(native,Ok(raw));
    }
}
#[cfg(kani)]
mod resume8_links {
    use std::os::unix::ffi::OsStrExt;
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn push_bytes() {
        let raw:[u8;2]=kani::any();let tail:[u8;1]=kani::any();
        if let (Ok(mut s),Ok(t))=(String::from_utf8(raw.to_vec()),std::str::from_utf8(&tail)) {
            let mut reference=raw.to_vec();reference.extend_from_slice(&tail);
            s.push_str(t);assert_eq!(s.as_bytes(),reference.as_slice());
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
fn push_bytes_negative() {
        let raw:[u8;2]=[65;2];let tail:[u8;1]=[66;1];
        if let (Ok(mut s),Ok(t))=(String::from_utf8(raw.to_vec()),std::str::from_utf8(&tail)) {
            let mut reference=raw.to_vec();reference.extend_from_slice(&tail);
            s.push_str(t);assert_ne!(s.as_bytes(),reference.as_slice());
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
fn join_two() {
        let a:[u8;2]=kani::any();let b:[u8;2]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=2 && m<=2);
        let p=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let q=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let native=p.join(q);let r=super::join_bytes_reference(&a[..n],&b[..m]);
        let i:usize=kani::any();
        assert_eq!(native.as_os_str().as_bytes().len(),r.len());
        assert_eq!(native.as_os_str().as_bytes().get(i),r.get(i));
    }
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn join_two_negative() {
        let a:[u8;2]=[65;2];let b:[u8;2]=[66;2];
        let n:usize=2;let m:usize=2;kani::assume(n<=2 && m<=2);
        let p=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let q=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let native=p.join(q);let r=super::join_bytes_reference(&a[..n],&b[..m]);
        let i:usize=0;
        assert_eq!(native.as_os_str().as_bytes().len(),r.len());
        assert_ne!(native.as_os_str().as_bytes().get(i),r.get(i));
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn array_reject_three() {
        let raw:[u32;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);
        let v=raw[..n].to_vec();let expected=raw[..n].to_vec();
        let native:Result<[u32;3],Vec<u32>>=v.try_into();
        assert_eq!(native,Err(expected));
    }
}

#[cfg(kani)]
mod resume9_links {
    fn load(b:[u8;4])->u32 {
        ((b[0] as u32)<<24u32)|((b[1] as u32)<<16u32)|((b[2] as u32)<<8u32)|(b[3] as u32)
    }
    fn store(w:u32)->[u8;4] {
        [(w>>24u32) as u8,(w>>16u32) as u8,(w>>8u32) as u8,w as u8]
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn load_be4() {let b:[u8;4]=kani::any();assert_eq!(u32::from_be_bytes(b),load(b));}
    #[kani::proof]
    #[kani::unwind(18)]
    fn store_be4() {let w:u32=kani::any();assert_eq!(w.to_be_bytes(),store(w));}
    fn pop_slices<T:Copy>(v:&[T],out:&mut Vec<T>)->Option<T> {
        if v.len()==0 {None} else {
            let last=v.len()-1;let mut i=0;
            while i<last {out.push(v[i]);i+=1;}
            Some(v[last])
        }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn pop_slices_u8() {
        let raw:[u8;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);
        let mut a=raw[..n].to_vec();let mut b=Vec::new();
        assert_eq!(a.pop(),pop_slices(&raw[..n],&mut b));
        let i:usize=kani::any();assert_eq!(a.len(),b.len());assert_eq!(a.get(i),b.get(i));
    }
    fn join_slices(base:&[u8],path:&[u8],out:&mut Vec<u8>) {
        if path.len()>0 && path[0]==b'/' {
            out.extend_from_slice(path);
        } else {
            out.extend_from_slice(base);
            if base.len()>0 && base[base.len()-1]!=b'/' {out.push(b'/');}
            out.extend_from_slice(path);
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
fn join_slices_two() {
        use std::os::unix::ffi::OsStrExt;
        let a:[u8;2]=kani::any();let b:[u8;2]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=2 && m<=2);
        let p=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let q=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let native=p.join(q);let mut reference=Vec::new();join_slices(&a[..n],&b[..m],&mut reference);
        let i:usize=kani::any();
        assert_eq!(native.as_os_str().as_bytes().len(),reference.len());
        assert_eq!(native.as_os_str().as_bytes().get(i),reference.get(i));
    }
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn join_slices_two_negative() {
        use std::os::unix::ffi::OsStrExt;
        let a:[u8;2]=[65;2];let b:[u8;2]=[66;2];
        let n:usize=2;let m:usize=2;kani::assume(n<=2 && m<=2);
        let p=std::path::Path::new(std::ffi::OsStr::from_bytes(&a[..n]));
        let q=std::path::Path::new(std::ffi::OsStr::from_bytes(&b[..m]));
        let native=p.join(q);let mut reference=Vec::new();join_slices(&a[..n],&b[..m],&mut reference);
        let i:usize=0;
        assert_eq!(native.as_os_str().as_bytes().len(),reference.len());
        assert_ne!(native.as_os_str().as_bytes().get(i),reference.get(i));
    }
}

#[macro_use] extern crate cfg_if;
extern crate libc;
extern crate getrandom;
#[path="/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4/src/error.rs"]
mod error;
use error::Error;
#[path="/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4/src/util_libc.rs"]
mod original;
use std::{cell::RefCell, mem::MaybeUninit};
#[derive(Clone)] enum Reply { Write(Vec<u8>), Err(i32), Raw(isize) }
fn call(replies: Vec<Reply>, initial: Vec<u8>) -> (Result<(),Error>,Vec<u8>,Vec<usize>) {
    let mut buffer:Vec<MaybeUninit<u8>>=initial.into_iter().map(MaybeUninit::new).collect();
    let queue=RefCell::new(replies.into_iter());let sizes=RefCell::new(Vec::new());
    let result=original::sys_fill_exact(&mut buffer, |b| {
        sizes.borrow_mut().push(b.len());
        match queue.borrow_mut().next().expect("boundary tape exhausted") {
            Reply::Write(bytes)=>{assert!(bytes.len()<=b.len()); for (d,v) in b.iter_mut().zip(bytes.iter()){d.write(*v);} bytes.len() as isize},
            Reply::Err(e)=>{unsafe{*libc::__errno_location()=e;} -1},
            Reply::Raw(r)=>r,
        }
    });
    (result,buffer.into_iter().map(|b|unsafe{b.assume_init()}).collect(),sizes.into_inner())
}
fn main(){
    let (r,b,s)=call(vec![],vec![]);assert!(r.is_ok());assert_eq!(b,Vec::<u8>::new());assert!(s.is_empty());
    let (r,b,s)=call(vec![Reply::Write(vec![7;64])],vec![9;64]);assert!(r.is_ok());assert_eq!(b,vec![7;64]);assert_eq!(s,vec![64]);
    let (r,b,s)=call(vec![Reply::Err(libc::EINTR),Reply::Write(vec![8;64])],vec![9;64]);assert!(r.is_ok());assert_eq!(b,vec![8;64]);assert_eq!(s,vec![64,64]);
    let (r,b,s)=call(vec![Reply::Write(vec![7;32]),Reply::Err(libc::EIO)],vec![9;64]);assert_eq!(r.unwrap_err().raw_os_error(),Some(libc::EIO));assert_eq!(b,[vec![7;32],vec![9;32]].concat());assert_eq!(s,vec![64,32]);
    for r in [0,-2,65] {let (e,b,s)=call(vec![Reply::Raw(r)],vec![9;64]);assert_eq!(e,Err(Error::UNEXPECTED));assert_eq!(b,vec![9;64]);assert_eq!(s,vec![64]);}
    let (a,_,sa)=call(vec![Reply::Err(libc::EIO)],vec![0;64]);
    let (b,_,sb)=call(vec![Reply::Write(vec![7;64])],vec![0;64]);
    assert!(a.is_err() && b.is_ok());assert_eq!(sa,sb);
    let mut live=[0u8;64];let live_ok=getrandom::fill(&mut live).is_ok();
    println!("{{\"cases\":8,\"original_sys_fill_exact\":true,\"same_request_different_failure_signal\":true,\"live_fill_success\":{live_ok},\"classification\":\"finite controlled-boundary validation; not a native witness-dependent failure counterexample\"}}");
}

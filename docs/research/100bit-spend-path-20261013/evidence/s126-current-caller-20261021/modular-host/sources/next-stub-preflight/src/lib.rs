#![allow(dead_code)]
trait NextStub: Iterator {fn next_stub(&mut self)->Option<Self::Item>;}
impl<'a,T> NextStub for std::slice::Iter<'a,T> {
 fn next_stub(&mut self)->Option<Self::Item> {None}
}
fn scan(b:&[u8])->bool {b.iter().any(|x|*x!=0)}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(3)]
#[kani::stub(<std::slice::Iter<u8> as core::iter::Iterator>::next, <std::slice::Iter<u8> as NextStub>::next_stub)]
fn next_guard_abstraction_preflight() {
 let b:[u8;4]=kani::any();assert!(!scan(&b));
 kani::cover!(b[0]!=0,"guard abstraction admits extra inputs");
}

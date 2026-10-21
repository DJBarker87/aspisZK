#![allow(dead_code)]
#[cfg(kani)]
trait AnyStub: Iterator {
 fn any_stub<F:FnMut(Self::Item)->bool>(&mut self,_:F)->bool {true}
}
#[cfg(kani)]
impl<I:Iterator> AnyStub for I {}
fn scan(b:&[u8])->bool {b.iter().any(|x|*x!=0)}
#[cfg(kani)]
#[kani::proof]
#[kani::stub(<std::slice::Iter<u8> as core::iter::Iterator>::any, AnyStub::any_stub)]
fn generic_any_stub_preflight() {
 let b:[u8;4]=kani::any();
 assert!(scan(&b));
 kani::cover!(b[0]!=0);
}

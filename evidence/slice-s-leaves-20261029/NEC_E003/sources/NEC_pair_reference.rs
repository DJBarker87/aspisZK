extern crate alloc;
use alloc::boxed::Box;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum ChildError<E> { Child(E) }
pub fn pair_ref<C,P,E>(common:C,reply:Result<P,E>)->Result<Box<(C,P)>,ChildError<E>> {
 match reply { Ok(public)=>Ok(Box::new((common,public))), Err(e)=>Err(ChildError::Child(e)) }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum ChildError<E> { Child(E) }
pub fn boxed_ref<T,E>(reply:Result<T,E>)->Result<Box<T>,ChildError<E>> {
 match reply { Ok(v)=>Ok(Box::new(v)), Err(e)=>Err(ChildError::Child(e)) }
}
pub fn relay_ref<T,E>(reply:Result<Box<T>,E>)->Result<Box<T>,ChildError<E>> {
 match reply { Ok(v)=>Ok(v), Err(e)=>Err(ChildError::Child(e)) }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum ChildError<E> { Child(E) }
pub fn reply_ref<T,E>(reply:Result<T,E>)->Result<T,ChildError<E>> {
 match reply { Ok(value)=>Ok(value),Err(error)=>Err(ChildError::Child(error)) }
}

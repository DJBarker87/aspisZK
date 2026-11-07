#[derive(Clone,Copy)] pub enum Error{Parse}
pub fn control_ref(n:usize,stop:usize)->(Result<(),Error>,usize){
 let mut calls=0;for j in 0..n{calls+=1;if j==stop{return(Err(Error::Parse),calls);}}
 (Ok(()),calls)
}

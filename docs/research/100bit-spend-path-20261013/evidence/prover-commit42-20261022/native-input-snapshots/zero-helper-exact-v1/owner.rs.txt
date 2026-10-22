//! Structural owner for the selected public-nonce 64-byte API.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Raw {pub field:[u8;32],pub leaf:[u8;32]}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Secret {pub nonce:[u8;32],pub raw:Raw}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error<E> {Os(E),RepeatedZero}
pub trait IO<S,E> {fn fill(state:S)->(Result<Raw,E>,S);}
// Kani-only helper substitution. proofs::zero_helper_exact checks the
// original recursive function at every call boundary used by generate/run.
pub fn zero(bytes:[u8;32],index:u8)->bool {
    assert_eq!(index,0);
    bytes==[0;32]
}

pub fn run<S,E,P:IO<S,E>>(nonce:[u8;32],fuel:u8,state:S)->(Result<Secret,Error<E>>,S) {
    if fuel==0 {return (Err(Error::RepeatedZero),state)}
    let (result,after)=P::fill(state);
    match result {
        Err(e)=>(Err(Error::Os(e)),after),
        Ok(raw)=>if !zero(raw.field,0) && !zero(raw.leaf,0) {(Ok(Secret{nonce,raw}),after)}
            else {run::<S,E,P>(nonce,fuel-1,after)}
    }
}
pub fn generate<S,E,P:IO<S,E>>(nonce:[u8;32],state:S)->(Result<Secret,Error<E>>,S) {
    if zero(nonce,0) {(Err(Error::RepeatedZero),state)} else {run::<S,E,P>(nonce,16,state)}
}

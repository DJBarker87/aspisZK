//! Structural reservation owner. No payload is supplied to the environment.
#[derive(Clone,Copy)]
pub enum Kind {Create,WriteMagic,WriteDigest,WriteNonce,FileSync,DirectoryOpen,DirectorySync}
pub enum Error<E> {Duplicate,Io(E)}
pub struct Run<S,E> {pub result:Result<(),Error<E>>,pub state:S,pub created:bool}
pub trait IO<S,E> {
    fn call(kind:Kind,state:S)->(Result<(),E>,S);
    fn duplicate(error:&E)->bool;
}
pub fn finish<S,E,P:IO<S,E>>(stage:u8,unix:bool,state:S)->Run<S,E> {
    let kind=if stage==0 {Kind::WriteMagic} else if stage==1 {Kind::WriteDigest}
        else if stage==2 {Kind::WriteNonce} else if stage==3 {Kind::FileSync}
        else if stage==4 {if unix {Kind::DirectoryOpen} else {return Run{result:Ok(()),state,created:true}}}
        else if stage==5 {Kind::DirectorySync} else {return Run{result:Ok(()),state,created:true}};
    let (outcome,after)=P::call(kind,state);
    match outcome {Err(e)=>Run{result:Err(Error::Io(e)),state:after,created:true},Ok(())=>finish::<S,E,P>(stage+1,unix,after)}
}
pub fn reserve<S,E,P:IO<S,E>>(unix:bool,state:S)->Run<S,E> {
    let (result,after)=P::call(Kind::Create,state);
    match result {
        Err(e)=>{let result=if P::duplicate(&e) {Err(Error::Duplicate)} else {Err(Error::Io(e))};Run{result,state:after,created:false}},
        Ok(())=>finish::<S,E,P>(0,unix,after),
    }
}

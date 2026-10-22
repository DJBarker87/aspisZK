#![allow(dead_code,unexpected_cfgs,static_mut_refs)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum Error {Transcript}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Table {key:[u8;2],value:Option<[u8;32]>,frame:[u8;32],calls:u8}
impl Table {
 fn insert(&mut self,a:[u8;2],v:[u8;32])->Option<[u8;32]> {
  // One-key projection of the existing TrustedStd insert law; frame is
  // retained. Every key/value at the source call boundary is arbitrary.
  assert_eq!(a,self.key);self.calls+=1;self.value.replace(v)
 }
}
fn native_merge(mut table:Table,transcript:Vec<([u8;2],[u8;32])>)->Result<Table,Error> {
        for (a,v) in transcript { if let Some(p)=table.insert(a,v) { if p!=v {return Err(Error::Transcript);} } }
 Ok(table)
}
#[cfg(kani)] mod proofs {use super::*;
 #[kani::proof] #[kani::unwind(40)]
 fn merge_call_boundary() {
  let key:[u8;2]=kani::any();let value:[u8;32]=kani::any();
  let previous:Option<[u8;32]>=kani::any();let frame:[u8;32]=kani::any();
  let table=Table{key,value:previous,frame,calls:0};
  let result=native_merge(table,vec![(key,value)]);
  let conflict=match previous {Some(old)=>old!=value,None=>false};
  match result {
   Err(Error::Transcript)=>assert!(conflict),
   Ok(after)=>{assert!(!conflict);assert_eq!(after.key,key);assert_eq!(after.value,Some(value));assert_eq!(after.frame,frame);assert_eq!(after.calls,1);}
  }
 }
}

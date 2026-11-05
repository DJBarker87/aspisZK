use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct HeapLog{failed:bool,calls:usize,returned:usize}
impl HeapLog{
 fn heap(&mut self,n:usize,value:u8)->Result<alloc::vec::Vec<u8>,aspis_core::r0::Error>{
  self.calls+=1;assert!(n==14759&&value==0);
  if self.failed {return Err(aspis_core::r0::Error::Allocation)}
  let out=alloc::vec![0u8;n];self.returned=out.as_ptr() as usize;Ok(out)
 }
}
fn heap_cut(log:&mut HeapLog)->Result<(),Error>{
 let mut logical=log.heap(compact::LOGICAL_SEMANTIC+compact::LOGICAL_Y1,0u8).map_err(|_|Error::Allocation)?;
 let (semantic,y1)=logical.split_at_mut(compact::LOGICAL_SEMANTIC-usize::from(cfg!(NHF_bad_stage)));
 assert!(semantic.as_ptr() as usize==log.returned&&semantic.len()==13831);
 assert!(y1.as_ptr() as usize==log.returned+13831&&y1.len()==928);
 Ok(())
}
struct ExpansionLog{proof:usize,logical:usize,stage:bool,calls:usize,failed:bool,observe:usize,reply:u8}
impl ExpansionLog{
 fn expand(&mut self,input:&[u8],out:&mut[u8])->Result<(),compact::CodecError>{
  self.calls+=1;
  if !self.stage{assert!(input.as_ptr() as usize==self.proof+16&&input.len()==7015&&out.as_ptr() as usize==self.logical&&out.len()==13831);}
  else{assert!(input.as_ptr() as usize==self.proof+7031&&input.len()==464&&out.as_ptr() as usize==self.logical+13831&&out.len()==928);}
  // Arbitrary observed-cell projection of the CLOSED callee's full output.
  // The caller itself never reads unobserved cells after this cut.
  let base=if self.stage{13831}else{0};
  if base<=self.observe&&self.observe<base+out.len(){out[self.observe-base]=self.reply;}
  if self.failed{Err(compact::CodecError::Length)}else{Ok(())}
 }
}
fn semantic_cut(proof:&[u8],logical:&mut[u8],log:&mut ExpansionLog)->Result<(),Error>{
 let (semantic,_y1)=logical.split_at_mut(compact::LOGICAL_SEMANTIC);
 log.expand(&proof[compact::OFF_SEMANTIC+usize::from(cfg!(NHF_bad_stage))..compact::OFF_Y1],semantic)?;
 Ok(())
}
fn values_cut(proof:&[u8],logical:&mut[u8],log:&mut ExpansionLog)->Result<(),Error>{
 let (_semantic,y1)=logical.split_at_mut(compact::LOGICAL_SEMANTIC);
 log.expand(&proof[compact::OFF_Y1+usize::from(cfg!(NHF_bad_stage))..compact::OFF_INACTIVE],y1)?;
 Ok(())
}
fn check_expand(stage:bool){
 let proof:[u8;57607]=kani::any();let mut logical:[u8;14759]=kani::any();
 let observe:usize=kani::any();kani::assume(observe<14759);let before=logical[observe];
 let mut log=ExpansionLog{proof:proof.as_ptr() as usize,logical:logical.as_ptr() as usize,stage,calls:0,failed:kani::any(),observe,reply:kani::any()};
 let result=if stage{values_cut(&proof,&mut logical,&mut log)}else{semantic_cut(&proof,&mut logical,&mut log)};
 assert_eq!(log.calls,1);
 assert!(match result{Ok(())=>!log.failed,Err(e)=>log.failed&&e==Error::Parse});
 let inside=if stage{13831<=observe}else{observe<13831};
 assert_eq!(logical[observe],if inside{log.reply}else{before});
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn heap_split(){let mut log=HeapLog{failed:kani::any(),calls:0,returned:0};let result=heap_cut(&mut log);assert_eq!(log.calls,1);assert!(match result{Ok(())=>!log.failed,Err(e)=>log.failed&&e==Error::Allocation});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_stage(){check_expand(false)}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn values_stage(){check_expand(true)}

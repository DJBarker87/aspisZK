use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn k()->K{let x:[u32;4]=kani::any();K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn kw(x:K,j:usize)->u32{match j{0=>x.c0.a.0,1=>x.c0.b.0,2=>x.c1.a.0,_=>x.c1.b.0}}
fn error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
struct ReadLog{base:usize,len:usize,at:usize,calls:usize,value:K,next:usize,error:Option<Error>}
impl ReadLog{fn read(&mut self,bytes:&[u8],at:usize)->Result<(K,usize),Error>{self.base=bytes.as_ptr() as usize;self.len=bytes.len();self.at=at;self.calls+=1;if let Some(e)=self.error{Err(e)}else{Ok((self.value,self.next))}}}
fn weight_step(bytes:&[u8],at:&mut usize,out:&mut K,log:&mut ReadLog)->Result<(),Error>{let(value,next)=log.read(bytes,*at)?;*at=next;*out=value;Ok(())}
fn weight_check<const C:usize>(){let bytes:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<64);let mut at=712+16*i;let before=k();let mut out=before;let value=k();let next:usize=kani::any();let err=if kani::any(){Some(error())}else{None};let mut log=ReadLog{base:0,len:0,at:0,calls:0,value,next,error:err};let mut result=weight_step(&bytes,&mut at,&mut out,&mut log);let j:usize=kani::any();kani::assume(j<4);if cfg!(NID_invert){match C{0=>log.base^=1,1=>at^=1,2=>{match j{0=>out.c0.a.0^=1,1=>out.c0.b.0^=1,2=>out.c1.a.0^=1,_=>out.c1.b.0^=1}},_=>result=match result{Ok(())=>Err(Error::Checkpoint),Err(_)=>Ok(())}}}let good=match C{0=>log.base==bytes.as_ptr() as usize&&log.len==1768&&log.at==712+16*i&&log.calls==1,1=>if err.is_some(){at==712+16*i}else{at==next},2=>kw(out,j)==kw(if err.is_some(){before}else{value},j),_=>match result{Err(e)=>Some(e)==err,Ok(())=>err.is_none()}};assert!(good);}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_entry(){weight_check::<0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_entry_renamed(){weight_check::<0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_cursor(){weight_check::<1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_cursor_renamed(){weight_check::<1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_value(){weight_check::<2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_value_renamed(){weight_check::<2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_result(){weight_check::<3>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn reader_result_renamed(){weight_check::<3>();}

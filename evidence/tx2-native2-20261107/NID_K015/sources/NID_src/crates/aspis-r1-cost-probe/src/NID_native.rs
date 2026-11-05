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
struct LeafLog<'a,const T:usize,const C:usize>{q:&'a[u8;832],reply:[u8;32],index:usize,calls:usize}
impl<const T:usize,const C:usize> LeafLog<'_,T,C>{fn digest(&mut self,parts:&[&[u8]])->[u8;32]{self.calls+=1;let(lo,width,salt,tag)=match T{0=>(0,480,608,0x71u8),1=>(480,128,640,0xf1u8),_=>(672,128,800,0x72u8)};let mut observed=if C==0{parts[0][self.index%2]as usize}else if C==1{parts[1][self.index%width]as usize}else if C==2{parts[2][self.index%32]as usize}else{parts.len()};if cfg!(NID_invert){observed^=1;}let expected=if C==0{[0x10u8,tag][self.index%2]as usize}else if C==1{self.q[lo+self.index%width]as usize}else if C==2{self.q[salt+self.index%32]as usize}else{3};assert_eq!(observed,expected);assert_eq!(parts[0].len(),2);assert_eq!(parts[1].len(),width);assert_eq!(parts[2].len(),32);assert_eq!(self.calls,1);self.reply}}
fn leaf_cut<const T:usize,const C:usize>(q:&[u8],log:&mut LeafLog<T,C>)->[u8;32]{match T{0=>{let salt:[u8;32]=q[608..640].try_into().unwrap();log.digest(&[&[0x10,merkle::C1_TAG],&q[..480],&salt])},1=>{let salt:[u8;32]=q[640..672].try_into().unwrap();log.digest(&[&[0x10,merkle::C2_TAG],&q[480..608],&salt])},_=>{let salt:[u8;32]=q[800..832].try_into().unwrap();log.digest(&[&[0x10,0x72],&q[672..800],&salt])}}}
fn leaf_check<const T:usize,const C:usize>(){let q:[u8;832]=kani::any();let reply:[u8;32]=kani::any();let index:usize=kani::any();kani::assume(index<480);let mut log=LeafLog::<T,C>{q:&q,reply,index,calls:0};let out=leaf_cut(&q,&mut log);assert_eq!(out[index%32],reply[index%32]);}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_tag(){leaf_check::<0,0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_tag_renamed(){leaf_check::<0,0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_payload(){leaf_check::<0,1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_payload_renamed(){leaf_check::<0,1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_salt(){leaf_check::<0,2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_salt_renamed(){leaf_check::<0,2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_shape(){leaf_check::<0,3>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf0_shape_renamed(){leaf_check::<0,3>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_tag(){leaf_check::<1,0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_tag_renamed(){leaf_check::<1,0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_payload(){leaf_check::<1,1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_payload_renamed(){leaf_check::<1,1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_salt(){leaf_check::<1,2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_salt_renamed(){leaf_check::<1,2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_shape(){leaf_check::<1,3>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf1_shape_renamed(){leaf_check::<1,3>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_tag(){leaf_check::<2,0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_tag_renamed(){leaf_check::<2,0>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_payload(){leaf_check::<2,1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_payload_renamed(){leaf_check::<2,1>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_salt(){leaf_check::<2,2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_salt_renamed(){leaf_check::<2,2>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_shape(){leaf_check::<2,3>();}

#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping, KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice, KMX_copy_from_slice)]
fn leaf2_shape_renamed(){leaf_check::<2,3>();}

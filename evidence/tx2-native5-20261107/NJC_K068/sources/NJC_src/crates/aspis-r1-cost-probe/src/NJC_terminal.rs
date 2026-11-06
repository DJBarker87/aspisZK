use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn e(x:[u32;8])->E{E::new(k([x[0],x[1],x[2],x[3]]),k([x[4],x[5],x[6],x[7]]))}
fn codec(x:u8)->crate::compact::CodecError{match x%3{0=>crate::compact::CodecError::Length,1=>crate::compact::CodecError::NonZeroHigh,_=>crate::compact::CodecError::NonCanonical}}
fn error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
struct Log<'a>{proof:&'a[u8],replies:[Option<Error>;4],calls:usize}
impl Log<'_>{fn record(&mut self,b:&[u8],mode:bool)->Result<(),Error>{let n=self.calls;let off=[7031usize,7495,7527,7783][n];let len=[464usize,32,224,2272][n];assert_eq!(b.as_ptr() as usize,self.proof.as_ptr() as usize+off);assert_eq!(b.len(),len^(if cfg!(NJC_invert){1}else{0}));assert!(!mode);self.calls+=1;match self.replies[n]{None=>Ok(()),Some(e)=>Err(e)}}
fn compact(&mut self,b:&[u8],c:crate::compact::CodecError)->Result<(),crate::compact::CodecError>{match self.record(b,false){Ok(())=>Ok(()),Err(_)=>Err(c)}}}
fn prefix(proof:&[u8],log:&mut Log,c:crate::compact::CodecError)->Result<(),Error>{log.compact(&proof[7031..7495],c)?;log.record(&proof[7495..7527],false)?;log.record(&proof[7527..7751],false)?;log.record(&proof[7783..10055],false)?;Ok(())}
fn prefix_check(){let proof:[u8;10055]=kani::any();let replies=core::array::from_fn(|_|if kani::any(){Some(error())}else{None});let mut log=Log{proof:&proof,replies,calls:0};let out=prefix(&proof,&mut log,codec(kani::any()));let mut expected=Ok(());let mut calls=4;let mut i=0;while i<4{if let Some(e)=replies[i]{expected=Err(if i==0{Error::Parse}else{e});calls=i+1;break;}i+=1;}assert_eq!(out,expected);assert_eq!(log.calls,calls);}
fn codec_check(){let out:Error=codec(kani::any()).into();assert_eq!(out,if cfg!(NJC_invert){Error::Allocation}else{Error::Parse});}
fn option_check(){let x:[u32;8]=kani::any();let present:bool=kani::any();let o=if present{Some(e(x))}else{None};let out=o.ok_or(Error::Parse);match out{Ok(v)=>{assert!(present);let mut expected=x;if cfg!(NJC_invert){expected[0]^=1;}assert_eq!(v.to_limbs(),expected);},Err(err)=>{assert!(!present);assert_eq!(err,if cfg!(NJC_bad_error){Error::Allocation}else{Error::Parse});}}}
fn r0(x:u8)->aspis_core::r0::Error{use aspis_core::r0::Error::*;match x%17{0=>IndexOutOfRange,1=>WrongLength,2=>ZeroDenominator,3=>Allocation,4=>NonCanonical,5=>WrongField,6=>InvalidPoints,7=>QuotientNotInImage,8=>RankDeficient,9=>Parse,10=>Semantic,11=>Schedule,12=>Sampler,13=>Commitment,14=>Authentication,15=>V1,_=>V2}}
fn map_check(){let a:[u32;4]=kani::any();let mut v=alloc::vec::Vec::new();v.push(k(a));let pointer=v.as_ptr() as usize;let len=v.len();let cap=v.capacity();let success:bool=kani::any();let input:Result<alloc::vec::Vec<K>,aspis_core::r0::Error>=if success{Ok(v)}else{Err(r0(kani::any()))};let out=input.map_err(|_|Error::Allocation);match out{Ok(w)=>{assert!(success);assert_eq!(w.as_ptr() as usize,pointer);assert_eq!(w.len(),len);assert_eq!(w.capacity(),cap);let mut expected=a;if cfg!(NJC_invert){expected[0]^=1;}let q=w[0];assert_eq!([q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0],expected);},Err(err)=>{assert!(!success);assert_eq!(err,if cfg!(NJC_bad_error){Error::Parse}else{Error::Allocation});}}}
fn closure_check(){let b:u8=kani::any();let mut pred=|&b:&u8|b!=0;let result=pred(&b);assert_eq!(result,(b!=0)^cfg!(NJC_invert));assert_eq!(core::mem::size_of_val(&pred),0);}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn scan_prefix(){prefix_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn scan_prefix_renamed(){prefix_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn codec_error(){codec_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn codec_error_renamed(){codec_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn option_e(){option_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn option_e_renamed(){option_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn map_allocation(){map_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn map_allocation_renamed(){map_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn header_predicate(){closure_check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn header_predicate_renamed(){closure_check();}

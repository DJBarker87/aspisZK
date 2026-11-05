use super::*;
use alloc::boxed::Box;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn raw_q()->QM31{let w:[u32;4]=kani::any();QM31{c0:aspis_core::field::CM31::new(aspis_core::field::M31(w[0]),aspis_core::field::M31(w[1])),c1:aspis_core::field::CM31::new(aspis_core::field::M31(w[2]),aspis_core::field::M31(w[3]))}}
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn error()->Error{let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag{0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
// One actual claims row-write boundary. Only the observed cell is initialized
// beforehand. Other cells remain MaybeUninit and are never read by this probe.
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_claim_row_write(){
 let p:usize=kani::any();kani::assume(p<3);let observe:usize=kani::any();kani::assume(observe<87);let limb:usize=kani::any();kani::assume(limb<4);let row:[QM31;29]=core::array::from_fn(|_|raw_q());let old=raw_q();let fail:bool=kani::any();let e=error();
 if cfg!(NHG_invert){kani::assume(!fail&&observe/29==p);}
 let mut out=Box::<[[QM31;29];3]>::new_uninit();let base=out.as_mut_ptr().cast::<QM31>();
 unsafe{base.add(observe).write(old);}
 let decoded=if fail{Err(e)}else{Ok(row)};
 let result=(||->Result<(),Error>{unsafe{out.as_mut_ptr().cast::<[QM31;29]>().add(p).write(decoded?);}Ok(())})();
 let got=unsafe{base.add(observe).read()};assert_eq!(result,if fail{Err(e)}else{Ok(())});let expected=if !fail&&observe/29==p{row[observe%29]}else{old};
 assert_eq!(words(got)[limb],words(expected)[limb]^if cfg!(NHG_invert){1}else{0});
}
struct DecodeLog{calls:usize,row:u8,ptr:*const u8,len:usize,byte:u8,observe:usize,offset:usize,fail:bool,error:Error,reply:[QM31;29]}
fn decode_cut(record:&ValidatedRecord<'_>,offset:usize,log:&mut DecodeLog)->Result<[QM31;29],Error>{log.calls+=1;log.row=record.row();let bytes=record.framed();log.ptr=bytes.as_ptr();log.len=bytes.len();log.byte=bytes[log.observe];log.offset=offset;if log.fail{Err(log.error)}else{Ok(log.reply)}}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_claim_decode_args(){
 let bytes=kani::vec::exact_vec::<u8,3717>();let record=ValidatedRecord{row:25,framed:&bytes};let p:usize=kani::any();kani::assume(p<3);let observe:usize=kani::any();kani::assume(observe<3717);let fail:bool=kani::any();let e=error();let reply:[QM31;29]=core::array::from_fn(|_|raw_q());let word:usize=kani::any();kani::assume(word<29);let limb:usize=kani::any();kani::assume(limb<4);let mut log=DecodeLog{calls:0,row:0,ptr:core::ptr::null(),len:0,byte:0,observe,offset:0,fail,error:e,reply};
 let got=decode_cut(&record,p*29,&mut log);assert_eq!(log.calls,1);assert_eq!(log.row,25);assert_eq!(log.ptr,bytes.as_ptr());assert_eq!(log.len,3717);assert_eq!(log.byte,bytes[observe]);assert_eq!(log.offset,p*29);
 if cfg!(NHG_invert){kani::assume(!fail);}
 match got{Err(actual)=>{assert!(fail);assert_eq!(actual,e)},Ok(row)=>{assert!(!fail);assert_eq!(words(row[word])[limb],words(reply[word])[limb]^if cfg!(NHG_invert){1}else{0});}}
}

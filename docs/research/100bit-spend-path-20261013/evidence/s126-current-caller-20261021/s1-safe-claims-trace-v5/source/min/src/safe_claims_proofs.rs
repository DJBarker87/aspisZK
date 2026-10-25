#![allow(static_mut_refs)]
use super::*;
type Row=[QM31;29];
type Claims=[Row;3];
static mut ROWS:Claims=[[QM31::ZERO;29];3];
static mut FAIL_AT:usize=3;
static mut ERROR:Error=Error::Public;
static mut CALLS:usize=0;
static mut FRAME_PTR:*const u8=core::ptr::null();
static mut FRAME_LEN:usize=0;
fn decode_stub<'a,const N:usize>(record:&wire::ValidatedRecord<'a>,offset:usize)->Result<[QM31;N],Error> where 'a:'a {
 unsafe {
  let p=CALLS;
  assert!(N==29);assert!(p<3);assert!(offset==p*29);
  assert!(record.row()==25);assert!(record.framed().as_ptr()==FRAME_PTR);assert!(record.framed().len()==FRAME_LEN);
  CALLS=p+1;
  if p==FAIL_AT{return Err(ERROR);}
  let mut row=[QM31::ZERO;N];let mut i=0;while i<N{row[i]=ROWS[p][i];i+=1;}Ok(row)
 }
}
fn raw_row()->Row{
 let mut row=[QM31::ZERO;29];let mut i=0;
 while i<29{row[i]=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any::<u32>()),b:aspis_core::field::M31(kani::any::<u32>())},c1:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any::<u32>()),b:aspis_core::field::M31(kani::any::<u32>())}};i+=1;}
 row
}
fn any_error()->Error{
 match kani::any::<u8>()%11{
  0=>Error::Allocation,1=>Error::RowOrder{expected:kani::any(),actual:kani::any()},2=>Error::InvalidRow,
  3=>Error::Tag{row:kani::any()},4=>Error::Length{row:kani::any()},5=>Error::NonCanonical{row:kani::any(),value:kani::any()},
  6=>Error::Boundary{round:kani::any()},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public,
 }
}

#[kani::proof]
#[kani::unwind(32)]
#[kani::stub(crate::r1_wire::ValidatedRecord::decode_k,decode_stub)]
fn native_claims_full_trace(){
 let rows=[raw_row(),raw_row(),raw_row()];let fail_at=(kani::any::<u8>()%4)as usize;let error=any_error();
 let frame=[0u8;3717];let length=(kani::any::<u16>()as usize)%3718;
 let framed=match frame.get(..length){Some(v)=>v,None=>{assert!(false);return;}};
 let root=[0u8;32];let prefix=wire::s1_claims_probe_prefix(&root,framed);
 unsafe{ROWS=rows;FAIL_AT=fail_at;ERROR=error;CALLS=0;FRAME_PTR=framed.as_ptr();FRAME_LEN=framed.len();}
 let result=claims(&prefix);let calls=unsafe{CALLS};
 let mut success=false;
 match result{
  Err(actual)=>{
   if calls==0{assert!(actual==Error::Allocation);}
   else{assert!(fail_at<3);assert!(calls==fail_at+1);assert!(actual==error);}
  }
  Ok(actual)=>{
   assert!(fail_at==3);assert!(calls==3);
   let mut p=0;while p<3{let mut i=0;while i<29{assert!(actual[p][i].c0.a==rows[p][i].c0.a);assert!(actual[p][i].c0.b==rows[p][i].c0.b);assert!(actual[p][i].c1.a==rows[p][i].c1.a);assert!(actual[p][i].c1.b==rows[p][i].c1.b);i+=1;}p+=1;}
   success=true;
  }
 }
 kani::cover!(fail_at==0&&calls==1,"first decode error returns immediately");
 kani::cover!(fail_at==2&&calls==3,"third decode error returns immediately");
 kani::cover!(success,"all three native rows returned");
}

// Direct paired native-result comparison; both complete bodies and allocation
// helpers execute. The only common normal-return cut is the decoder.
#[kani::proof]
#[kani::unwind(32)]
#[kani::stub(crate::r1_wire::ValidatedRecord::decode_k,decode_stub)]
fn paired_frozen_safe_claims(){
 let rows=[raw_row(),raw_row(),raw_row()];let fail_at=(kani::any::<u8>()%4)as usize;let error=any_error();
 let frame=[0u8;3717];let length=(kani::any::<u16>()as usize)%3718;
 let framed=match frame.get(..length){Some(v)=>v,None=>{assert!(false);return;}};
 let root=[0u8;32];let prefix=wire::s1_claims_probe_prefix(&root,framed);
 unsafe{ROWS=rows;FAIL_AT=fail_at;ERROR=error;CALLS=0;FRAME_PTR=framed.as_ptr();FRAME_LEN=framed.len();}
 let original=crate::original_claims::run(&prefix);let first_calls=unsafe{CALLS};
 unsafe{CALLS=0;}
 let candidate=claims(&prefix);let second_calls=unsafe{CALLS};
 assert!(first_calls==second_calls);
 let mut success=false;
 match (original,candidate){
  (Err(a),Err(b))=>{assert!(a==b);}
  (Ok(a),Ok(b))=>{
   let mut p=0;while p<3{let mut i=0;while i<29{
    assert!(a[p][i].c0.a==b[p][i].c0.a);assert!(a[p][i].c0.b==b[p][i].c0.b);
    assert!(a[p][i].c1.a==b[p][i].c1.a);assert!(a[p][i].c1.b==b[p][i].c1.b);i+=1;}p+=1;}
   success=true;
  }
  _=>{assert!(false);}
 }
 kani::cover!(fail_at==0&&first_calls==1,"paired first decoder rejection");
 kani::cover!(fail_at==2&&first_calls==3,"paired third decoder rejection");
 kani::cover!(success,"paired complete native Claims results");
}

// EXCLUDED negative control: only the final expected field word differs.
#[kani::proof]
#[kani::unwind(32)]
#[kani::stub(crate::r1_wire::ValidatedRecord::decode_k,decode_stub)]
fn paired_frozen_safe_claims_negative_last_word(){
 let rows=[raw_row(),raw_row(),raw_row()];let fail_at=(kani::any::<u8>()%4)as usize;let error=any_error();
 let frame=[0u8;3717];let length=(kani::any::<u16>()as usize)%3718;
 let framed=match frame.get(..length){Some(v)=>v,None=>{assert!(false);return;}};
 let root=[0u8;32];let prefix=wire::s1_claims_probe_prefix(&root,framed);
 unsafe{ROWS=rows;FAIL_AT=fail_at;ERROR=error;CALLS=0;FRAME_PTR=framed.as_ptr();FRAME_LEN=framed.len();}
 let original=crate::original_claims::run(&prefix);let first_calls=unsafe{CALLS};
 unsafe{CALLS=0;}
 let candidate=claims(&prefix);let second_calls=unsafe{CALLS};
 assert!(first_calls==second_calls);
 let mut success=false;
 match (original,candidate){
  (Err(a),Err(b))=>{assert!(a==b);}
  (Ok(a),Ok(b))=>{
   let mut p=0;while p<3{let mut i=0;while i<29{
    assert!(a[p][i].c0.a==b[p][i].c0.a);assert!(a[p][i].c0.b==b[p][i].c0.b);
    assert!(a[p][i].c1.a==b[p][i].c1.a);assert!(a[p][i].c1.b.0==(b[p][i].c1.b.0 ^ if p==2&&i==28{1}else{0}));i+=1;}p+=1;}
   success=true;
  }
  _=>{assert!(false);}
 }
 kani::cover!(fail_at==0&&first_calls==1,"paired first decoder rejection");
 kani::cover!(fail_at==2&&first_calls==3,"paired third decoder rejection");
 kani::cover!(success,"paired complete native Claims results");
}

#![allow(static_mut_refs)]
// Inside the unchanged frozen r1_semantic module: actual private token,
// actual WireError, full QM31 and actual Box<MaybeUninit<[[QM31;29];3]>>.
use super::*;
use core::mem::MaybeUninit;
type Row = [QM31;29];
type Claims = [Row;3];
static mut DECODED: Row = [QM31::ZERO;29];
static mut FAILURE: Option<Error> = None;
static mut CALLS: usize = 0;
static mut OFFSET: usize = 0;
static mut RECORD_ROW: u8 = 0;
static mut RECORD_PTR: *const u8 = core::ptr::null();
static mut RECORD_LEN: usize = 0;

fn decode_stub<const N:usize>(record:&wire::ValidatedRecord<'_>,offset_values:usize)->Result<[QM31;N],Error>{
 unsafe{
  assert_eq!(N,29);assert_eq!(CALLS,0);CALLS=1;
  assert_eq!(offset_values,OFFSET);assert_eq!(record.row(),RECORD_ROW);
  assert_eq!(record.framed().as_ptr(),RECORD_PTR);assert_eq!(record.framed().len(),RECORD_LEN);
  if let Some(error)=FAILURE{return Err(error);}
  let mut out=[QM31::ZERO;N];let mut i=0;
  while i<N {out[i]=DECODED[i];i+=1;}
  Ok(out)
 }
}

// Verbatim one iteration of the shipped claims loop, including the real
// decoded-array callee and its early-return operator. Allocation is outside
// this fragment, and is not replaced by an opaque success assumption.
fn native_step(record:wire::ValidatedRecord<'_>,out:&mut Box<MaybeUninit<Claims>>,p:usize)->Result<(),Error>{
 unsafe {
  out.as_mut_ptr()
      .cast::<[QM31; 29]>()
      .add(p)
      .write(record.decode_k::<29>(p * 29)?);
 }
 Ok(())
}
fn owned_step(mut before:Claims,p:usize,decoded:Result<Row,Error>)->(Result<(),Error>,Claims){
 match decoded {Err(error)=>(Err(error),before),Ok(row)=>{before[p]=row;(Ok(()),before)}}
}
fn row(raw:[[u32;4];29])->Row{
 let mut out=[QM31::ZERO;29];let mut i=0;
 while i<29 {
  out[i]=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(raw[i][0]),b:aspis_core::field::M31(raw[i][1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(raw[i][2]),b:aspis_core::field::M31(raw[i][3])}};i+=1;
 }
 out
}
fn any_error()->Error{
 match kani::any::<u8>()%11{
  0=>Error::Allocation,1=>Error::RowOrder{expected:kani::any(),actual:kani::any()},2=>Error::InvalidRow,
  3=>Error::Tag{row:kani::any()},4=>Error::Length{row:kani::any()},5=>Error::NonCanonical{row:kani::any(),value:kani::any()},
  6=>Error::Boundary{round:kani::any()},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public,
 }
}
fn same_row(a:&Row,b:&Row){
 let mut i=0;while i<29{
  assert_eq!(a[i].c0.a,b[i].c0.a);assert_eq!(a[i].c0.b,b[i].c0.b);
  assert_eq!(a[i].c1.a,b[i].c1.a);assert_eq!(a[i].c1.b,b[i].c1.b);i+=1;
 }
}
#[kani::proof]
#[kani::unwind(32)]
#[kani::stub(crate::r1_wire::ValidatedRecord::decode_k,decode_stub)]
fn claims_row_write_preserves_initialized_prefix(){
 assert_eq!(core::mem::size_of::<QM31>(),16);
 assert_eq!(core::mem::size_of::<Row>(),464);
 assert_eq!(core::mem::size_of::<Claims>(),1392);
 assert_eq!(core::mem::align_of::<Claims>(),core::mem::align_of::<Row>());
 assert!(!core::mem::needs_drop::<QM31>());
 let p=(kani::any::<u8>()%3)as usize;
 let before=[row(kani::any()),row(kani::any()),row(kani::any())];
 let decoded=row(kani::any());let failure=if kani::any::<bool>(){Some(any_error())}else{None};
 let mut out=Box::new(MaybeUninit::<Claims>::uninit());
 // Only earlier rows are initialized, as in the actual loop invariant.
 let mut i=0;while i<p{unsafe{out.as_mut_ptr().cast::<Row>().add(i).write(before[i]);}i+=1;}
 // Byte contents are deliberately unread by the abstracted verified decoder.
 // The complete real token's row/pointer/length are checked at the call site.
 let framed=[0u8;3717];let length=(kani::any::<u16>()as usize)%3718;
 let record=wire::s1_claims_probe_record(kani::any(),&framed[..length]);
 unsafe{DECODED=decoded;FAILURE=failure;CALLS=0;OFFSET=p*29;RECORD_ROW=record.row();RECORD_PTR=record.framed().as_ptr();RECORD_LEN=record.framed().len();}
 let result=native_step(record,&mut out,p);
 let (expected,reference)=owned_step(before,p,match failure{Some(e)=>Err(e),None=>Ok(decoded)});
 assert_eq!(result,expected);assert_eq!(unsafe{CALLS},1);
 let initialized=p+usize::from(result.is_ok());
 i=0;while i<initialized{
  let actual=unsafe{out.as_ptr().cast::<Row>().add(i).read()};same_row(&actual,&reference[i]);i+=1;
 }
 // Last successful iteration yields the complete real output Box, rather
 // than reading an uninitialized suffix or substituting an output token.
 if p==2&&result.is_ok(){
  let complete=unsafe{out.assume_init()};i=0;while i<3{same_row(&complete[i],&reference[i]);i+=1;}
 }
 kani::cover!(p==0&&result.is_err(),"first row rejects before write");
 kani::cover!(p==2&&result.is_err(),"third row rejects preserving prior rows");
 kani::cover!(p==2&&result.is_ok(),"complete initialized native Box");
}

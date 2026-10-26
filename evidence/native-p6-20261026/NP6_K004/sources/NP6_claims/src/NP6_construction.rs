//! Construction cut only, NOT the complete Claims body or decoder proof.
//! The literal unsafe write expression follows a shared Result-valued decode cut.
use crate::r1_wire::Error;
use alloc::boxed::Box;
use aspis_core::field::{QM31,CM31,M31};
type Row=[QM31;29];
type Claims=[Row;3];
fn row(raw:[[u32;4];29])->Row {
 let mut out=[QM31::ZERO;29];
 for j in 0..29 {out[j]=QM31{c0:CM31{a:M31(raw[j][0]),b:M31(raw[j][1])},c1:CM31{a:M31(raw[j][2]),b:M31(raw[j][3])}};}
 out
}
fn native(rows:[Row;3],failure:u8,error:Error)->Result<Box<Claims>,Error>{
 let mut out=aspis_core::r0::heap::uninit::<Claims>().map_err(|_|Error::Allocation)?;
 unsafe {
  for p in 0..3 {
   out.as_mut_ptr().cast::<Row>().add(p).write(if failure==p as u8 {Err(error)} else {Ok(rows[p])}?);
  }
  Ok(out.assume_init())
 }
}
fn owned(rows:[Row;3],failure:u8,error:Error)->Result<Box<Claims>,Error>{
 let rows0=aspis_core::r0::heap::filled(3,[QM31::ZERO;29]).map_err(|_|Error::Allocation)?;
 let mut out:Box<Claims>=rows0.into_boxed_slice().try_into().map_err(|_|Error::Allocation)?;
 out[0]=if failure==0 {Err(error)} else {Ok(rows[0])}?;
 out[1]=if failure==1 {Err(error)} else {Ok(rows[1])}?;
 out[2]=if failure==2 {Err(error)} else {Ok(rows[2])}?;
 Ok(out)
}
#[kani::proof]
#[kani::unwind(32)]
fn NP6_construct_arbitrary_results(){
 let rows=[row(kani::any()),row(kani::any()),row(kani::any())];
 let failure=kani::any::<u8>();
 let error=Error::NonCanonical{row:kani::any(),value:kani::any()};
 let a=native(rows,failure,error);
 let b=owned(rows,failure,error);
 match (a,b){
  (Ok(a),Ok(b))=>{let i=(kani::any::<u8>()%3) as usize;let j=(kani::any::<u8>()%29) as usize;assert_eq!(a[i][j],b[i][j]);kani::cover!(true,"native initialized box returns arbitrary contents");},
  (Err(a),Err(b))=>{assert_eq!(a,b);kani::cover!(failure==2,"third decode error drops partial native allocation");},
  _=>panic!("construction Result mismatch"),
 }
}

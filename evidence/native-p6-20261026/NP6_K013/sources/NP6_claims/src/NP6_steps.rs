//! One complete real decode/write iteration, not a whole Claims theorem.
use crate::r1_wire::{self as wire,Error};
use alloc::boxed::Box;
use core::mem::MaybeUninit;
use aspis_core::field::{QM31,CM31,M31};
type Row=[QM31;29];type Claims=[Row;3];
fn row(raw:[[u32;4];29])->Row {
 let mut out=[QM31::ZERO;29];
 for j in 0..29 {out[j]=QM31{c0:CM31{a:M31(raw[j][0]),b:M31(raw[j][1])},c1:CM31{a:M31(raw[j][2]),b:M31(raw[j][3])}};}
 out
}
// Verbatim pointer/write/decode expression of one shipped loop iteration.
fn native_step<const P:usize>(record:&wire::ValidatedRecord<'_>,out:&mut Box<MaybeUninit<Claims>>)->Result<(),Error>{
 unsafe {out.as_mut_ptr().cast::<[QM31;29]>().add(P).write(record.decode_k::<29>(P*29)?);}
 Ok(())
}
fn owned_step<const P:usize>(record:&wire::ValidatedRecord<'_>,out:&mut Claims)->Result<(),Error>{
 out[P]=record.decode_k::<29>(P*29)?;
 Ok(())
}
fn check<const P:usize>(){
 let before=[row(kani::any()),row(kani::any()),row(kani::any())];
 let framed:[u8;3717]=kani::any();let root=[0u8;32];
 let prefix=wire::np6_prefix(&root,&framed);
 let record=prefix.validated_record(25).unwrap();
 let mut native=aspis_core::r0::heap::uninit::<Claims>().unwrap();
 for j in 0..P {unsafe{native.as_mut_ptr().cast::<Row>().add(j).write(before[j]);}}
 let mut owned=before;
 let a=native_step::<P>(&record,&mut native);let b=owned_step::<P>(&record,&mut owned);
 assert!(a==b);
 let initialized=P+usize::from(a.is_ok());
 if initialized>0 {
  let i=(kani::any::<u8>()as usize)%initialized;
  let j=(kani::any::<u8>()as usize)%29;
  assert!(unsafe{(*native.as_ptr().cast::<Row>().add(i))[j]}==owned[i][j]);
 }
 if P==2&&a.is_ok(){
  let native=unsafe{native.assume_init()};
  let i=(kani::any::<u8>()as usize)%3;let j=(kani::any::<u8>()as usize)%29;
  assert!(native[i][j]==owned[i][j]);
 }
}
#[kani::proof] #[kani::unwind(32)] fn NP6_decode_write_p0(){check::<0>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_decode_write_p1(){check::<1>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_decode_write_p2(){check::<2>();}

use super::*;
#[path="NFQ_scan_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(readonly_buffer_meta_ok)]
fn readonly_contract(){let _=readonly_buffer_meta_ok(kani::any(),kani::any(),kani::any());}

// ONE frozen loop iteration. Tag 2 is a continuation, not native success.
fn zero_cut(mut remaining:&[u8])->(u8,&[u8],ProgramResult){
 if !remaining.is_empty(){
  if remaining[0]!=0{return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));}
  remaining=&remaining[1..];
  return (2,remaining,Ok(()));
 }
 (0,remaining,Ok(()))
}
#[kani::proof]
fn zero_result_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let (tag,_,r)=zero_cut(&bytes[..n]);let want=if n==0{0}else if bytes[0]!=0{1}else{2};
 let full=tag==want && if tag==1{matches!(r,Err(ProgramError::AccountAlreadyInitialized))}else{r.is_ok()};
 assert!(full != cfg!(NFQ_invert));
 kani::cover!(tag==0);kani::cover!(tag==1);kani::cover!(tag==2);
}
#[kani::proof]
fn zero_length_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let (tag,rest,_)=zero_cut(&bytes[..n]);let shift=if tag==2{1}else{0};
 assert!((rest.len()==n-shift) != cfg!(NFQ_invert));
}
#[kani::proof]
fn zero_pointer_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);let view=&bytes[..n];
 let (tag,rest,_)=zero_cut(view);let shift=if tag==2{1}else{0};
 assert!((rest.as_ptr()==view.as_ptr().wrapping_add(shift)) != cfg!(NFQ_invert));
}
#[kani::proof]
fn zero_frame_window(){
 let bytes:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);
 let a=bytes[0];let b=bytes[1];let c=bytes[2];let d=bytes[3];
 let _=zero_cut(&bytes[..n]);
 assert!((bytes[0]==a&&bytes[1]==b&&bytes[2]==c&&bytes[3]==d) != cfg!(NFQ_invert));
}

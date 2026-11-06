#[derive(Default)]
struct OpenLog{calls:usize,proof_ptr:usize,proof_len:usize,ordinal:usize,ptr:usize,len:usize}
fn scan_open_step<'a>(proof:&'a[u8],iter:&mut core::ops::Range<usize>,log:&mut OpenLog)->Option<&'a[u8]>{
 match iter.next(){
  None=>None,
  Some(i)=>{
   log.calls+=1;log.proof_ptr=proof.as_ptr()as usize;log.proof_len=proof.len();log.ordinal=i;
   let q=opening(proof,i);log.ptr=q.as_ptr()as usize;log.len=q.len();Some(q)
  }
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_open_iteration(){
 let proof:[u8;57607]=kani::any();let start:usize=kani::any();kani::assume(start<=22);
 #[cfg(NKL_argument_control)] kani::assume(start<22);
 let active=start<22;let mut iter=start..22;let mut log=OpenLog::default();let probe:usize=kani::any();kani::assume(probe<57607);let before=proof[probe];
 let out=scan_open_step(&proof,&mut iter,&mut log);
 #[cfg(not(NKL_value_control))] assert_eq!(out.is_some(),active);
 #[cfg(NKL_value_control)] assert_ne!(out.is_some(),active);
 assert_eq!(iter.start,if active{start+1}else{start});assert_eq!(iter.end,22);
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,active as usize);
 #[cfg(NKL_invert)] assert_ne!(log.calls,active as usize);
 #[cfg(not(NKL_frame_control))] assert_eq!(proof[probe],before);
 #[cfg(NKL_frame_control)] assert_ne!(proof[probe],before);
 if let Some(q)=out{
  assert_eq!(log.proof_ptr,proof.as_ptr()as usize);assert_eq!(log.proof_len,57607);assert_eq!(log.ordinal,start);assert_eq!(log.len,832);assert_eq!(q.len(),832);assert_eq!(log.ptr,q.as_ptr()as usize);
  #[cfg(not(NKL_argument_control))] assert_eq!(q.as_ptr(),proof.as_ptr().wrapping_add(10055+start*832));
  #[cfg(NKL_argument_control)] assert_ne!(q.as_ptr(),proof.as_ptr().wrapping_add(10055+start*832));
 }else{assert_eq!(log.proof_ptr,0);assert_eq!(log.proof_len,0);assert_eq!(log.ptr,0);assert_eq!(log.len,0)}
}
fn scan_slot_boundary(q:&[u8],iter:&mut core::ops::Range<usize>,log:&mut ScanCallLog)->Result<Option<usize>,Error>{
 match iter.next(){
  Some(s)=>Ok(Some(s)),
  None=>{
   let bytes=&q[672..800];log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();log.flag=false;
   let reply=echeck(bytes,false);log.reply_ok=reply.is_ok();reply?;Ok(None)
  }
 }
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(super::echeck,arbitrary_echeck)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_slot_iteration(){
 let q:[u8;832]=kani::any();let start:usize=kani::any();kani::assume(start<=4);
 #[cfg(any(NKL_argument_control,NKL_value_control))] kani::assume(start==4);
 let active=start<4;let mut iter=start..4;let mut log=ScanCallLog::default();let probe:usize=kani::any();kani::assume(probe<832);let before=q[probe];
 let out=scan_slot_boundary(&q,&mut iter,&mut log);let expected=active||log.reply_ok;
 #[cfg(not(NKL_value_control))] assert_eq!(out.is_ok(),expected);
 #[cfg(NKL_value_control)] assert_ne!(out.is_ok(),expected);
 assert_eq!(iter.start,if active{start+1}else{start});assert_eq!(iter.end,4);
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,(!active)as usize);
 #[cfg(NKL_invert)] assert_ne!(log.calls,(!active)as usize);
 #[cfg(not(NKL_frame_control))] assert_eq!(q[probe],before);
 #[cfg(NKL_frame_control)] assert_ne!(q[probe],before);
 if active{assert!(matches!(out,Ok(Some(s))if s==start));assert_eq!(log.ptr,0);assert_eq!(log.len,0)}
 else{
  if log.reply_ok{assert!(matches!(out,Ok(None)))}else{assert!(matches!(out,Err(Error::Parse)))}
  #[cfg(not(NKL_argument_control))] assert_eq!(log.ptr,q.as_ptr().wrapping_add(672)as usize);
  #[cfg(NKL_argument_control)] assert_ne!(log.ptr,q.as_ptr().wrapping_add(672)as usize);
  assert_eq!(log.len,128);assert!(!log.flag)
 }
}

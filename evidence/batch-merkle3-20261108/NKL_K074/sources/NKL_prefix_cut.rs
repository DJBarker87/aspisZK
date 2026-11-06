fn scan_prefix_call(proof:&[u8],site:usize,log:&mut ScanCallLog)->Result<(),Error>{
 match site{
  0=>{
   let bytes=&proof[compact::OFF_Y1..compact::OFF_INACTIVE];log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();
   let reply=compact::check_values(bytes);log.reply_ok=reply.is_ok();reply?;Ok(())
  },
  1=>{
   let bytes=&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE+32];log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();log.flag=false;
   let reply=echeck(bytes,false);log.reply_ok=reply.is_ok();reply?;Ok(())
  },
  2=>{
   let bytes=&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT];log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();log.flag=false;
   let reply=echeck(bytes,false);log.reply_ok=reply.is_ok();reply?;Ok(())
  },
  _=>{
   let bytes=&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS];log.calls+=1;log.ptr=bytes.as_ptr()as usize;log.len=bytes.len();log.flag=false;
   let reply=echeck(bytes,false);log.reply_ok=reply.is_ok();reply?;Ok(())
  }
 }
}
#[kani::proof]
#[kani::unwind(2)]
#[kani::stub(super::echeck,arbitrary_echeck)]
#[kani::stub(compact::check_values,arbitrary_compact)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_prefix_call_cut(){
 let proof:[u8;57607]=kani::any();let site:usize=kani::any();kani::assume(site<4);let mut log=ScanCallLog::default();
 let probe:usize=kani::any();kani::assume(probe<57607);let before=proof[probe];
 let out=scan_prefix_call(&proof,site,&mut log);
 #[cfg(not(NKL_value_control))] assert_eq!(out.is_ok(),log.reply_ok);
 #[cfg(NKL_value_control)] assert_ne!(out.is_ok(),log.reply_ok);
 if !log.reply_ok{assert!(matches!(out,Err(Error::Parse)))}
 let(start,len)=match site{0=>(7031,464),1=>(7495,32),2=>(7527,224),_=>(7783,2272)};
 #[cfg(not(NKL_argument_control))] assert_eq!(log.ptr,proof.as_ptr().wrapping_add(start)as usize);
 #[cfg(NKL_argument_control)] assert_ne!(log.ptr,proof.as_ptr().wrapping_add(start)as usize);
 assert_eq!(log.len,len);assert!(!log.flag);
 #[cfg(not(NKL_frame_control))] assert_eq!(proof[probe],before);
 #[cfg(NKL_frame_control)] assert_ne!(proof[probe],before);
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,1);
 #[cfg(NKL_invert)] assert_ne!(log.calls,1);
}

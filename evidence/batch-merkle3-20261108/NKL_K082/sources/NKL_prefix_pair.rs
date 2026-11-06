fn scan_prefix_two(proof:&[u8],first:&mut ScanCallLog,second:&mut ScanCallLog)->Result<(),Error>{
 scan_prefix_call(proof,0,first)?;
 scan_prefix_call(proof,1,second)?;
 Ok(())
}
#[kani::proof]
#[kani::unwind(2)]
#[kani::stub(super::echeck,arbitrary_echeck)]
#[kani::stub(crate::compact::check_values,arbitrary_compact)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_prefix_two_cut(){
 let proof:[u8;57607]=kani::any();let probe:usize=kani::any();kani::assume(probe<57607);let before=proof[probe];
 let mut first=ScanCallLog::default();let mut second=ScanCallLog::default();
 let out=scan_prefix_two(&proof,&mut first,&mut second);
 assert_eq!(first.calls,1);assert_eq!(first.ptr,proof.as_ptr().wrapping_add(compact::OFF_Y1)as usize);assert_eq!(first.len,464);
 assert_eq!(out.is_ok(),first.reply_ok&&second.reply_ok);assert_eq!(proof[probe],before);
 if out.is_err(){assert!(matches!(out,Err(Error::Parse)))}
 #[cfg(not(NKL_invert))] assert_eq!(second.calls,first.reply_ok as usize);
 #[cfg(NKL_invert)] assert_ne!(second.calls,first.reply_ok as usize);
 if first.reply_ok{assert_eq!(second.ptr,proof.as_ptr().wrapping_add(compact::OFF_INACTIVE)as usize);assert_eq!(second.len,32);assert!(!second.flag)}
 else{assert_eq!(second.ptr,0);assert_eq!(second.len,0);assert!(!second.reply_ok)}
}

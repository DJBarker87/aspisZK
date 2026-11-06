#[derive(Default)]
struct ScanLog{calls:usize,offset:usize,width:usize}
fn scan_scalar_step(q:&[u8],s:usize,iter:&mut core::ops::Range<usize>,log:&mut ScanLog)->Result<(),Error>{
 match iter.next(){
  None=>Ok(()),
  Some(l)=>{
   log.calls+=1;log.offset=s*120+l*4;log.width=4;
   M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
   Ok(())
  }
 }
}
fn scan_k_step(q:&[u8],s:usize,iter:&mut core::ops::Range<usize>,log:&mut ScanLog)->Result<(),Error>{
 match iter.next(){
  None=>Ok(()),
  Some(l)=>{
   log.calls+=1;log.offset=480+s*32+l*16;log.width=16;
   K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
   Ok(())
  }
 }
}
fn scan_c1_step(q:&[u8],s:usize,log:&mut ScanLog)->Result<(),Error>{
 log.calls+=1;log.offset=s*120+104;log.width=16;
 K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
 Ok(())
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_scalar_iteration(){
 let q:[u8;832]=kani::any();let probe:usize=kani::any();kani::assume(probe<832);let before=q[probe];let s:usize=kani::any();let start:usize=kani::any();kani::assume(s<4&&start<=26); #[cfg(any(NKL_value_control,NKL_frame_control))] kani::assume(start<26);
 let mut iter=start..26;let mut log=ScanLog::default();let active=start<26;let offset=s*120+start*4;
 let expected=if active{u32::from_le_bytes(q[offset..offset+4].try_into().unwrap())<2147483647}else{true};
 let out=scan_scalar_step(&q,s,&mut iter,&mut log); #[cfg(not(NKL_frame_control))] assert_eq!(q[probe],before); #[cfg(NKL_frame_control)] assert_ne!(q[probe],before);
 assert_eq!(iter.start,if active{start+1}else{start});assert_eq!(iter.end,26);#[cfg(not(NKL_value_control))] assert_eq!(out.is_ok(),expected); #[cfg(NKL_value_control)] assert_ne!(out.is_ok(),expected);if !expected{assert!(matches!(out,Err(Error::Parse)))}
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,active as usize);
 #[cfg(NKL_invert)] assert_ne!(log.calls,active as usize);
 if active{assert_eq!(log.offset,offset);assert_eq!(log.width,4)}else{assert_eq!(log.offset,0);assert_eq!(log.width,0)}
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_k_iteration(){
 let q:[u8;832]=kani::any();let probe:usize=kani::any();kani::assume(probe<832);let before=q[probe];let s:usize=kani::any();let start:usize=kani::any();kani::assume(s<4&&start<=2); #[cfg(any(NKL_value_control,NKL_frame_control))] kani::assume(start<2);
 let mut iter=start..2;let mut log=ScanLog::default();let active=start<2;let offset=480+s*32+start*16;
 let w=|at:usize|u32::from_le_bytes(q[at..at+4].try_into().unwrap());let expected=if active{w(offset)<2147483647&&w(offset+4)<2147483647&&w(offset+8)<2147483647&&w(offset+12)<2147483647}else{true};
 let out=scan_k_step(&q,s,&mut iter,&mut log); #[cfg(not(NKL_frame_control))] assert_eq!(q[probe],before); #[cfg(NKL_frame_control)] assert_ne!(q[probe],before);
 assert_eq!(iter.start,if active{start+1}else{start});assert_eq!(iter.end,2);#[cfg(not(NKL_value_control))] assert_eq!(out.is_ok(),expected); #[cfg(NKL_value_control)] assert_ne!(out.is_ok(),expected);if !expected{assert!(matches!(out,Err(Error::Parse)))}
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,active as usize);
 #[cfg(NKL_invert)] assert_ne!(log.calls,active as usize);
 if active{assert_eq!(log.offset,offset);assert_eq!(log.width,16)}else{assert_eq!(log.offset,0);assert_eq!(log.width,0)}
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn scan_c1_iteration(){
 let q:[u8;832]=kani::any();let probe:usize=kani::any();kani::assume(probe<832);let before=q[probe];let s:usize=kani::any();kani::assume(s<4);let mut log=ScanLog::default();let offset=s*120+104;
 let w=|at:usize|u32::from_le_bytes(q[at..at+4].try_into().unwrap());let expected=w(offset)<2147483647&&w(offset+4)<2147483647&&w(offset+8)<2147483647&&w(offset+12)<2147483647;
 let out=scan_c1_step(&q,s,&mut log); #[cfg(not(NKL_frame_control))] assert_eq!(q[probe],before); #[cfg(NKL_frame_control)] assert_ne!(q[probe],before);#[cfg(not(NKL_value_control))] assert_eq!(out.is_ok(),expected); #[cfg(NKL_value_control)] assert_ne!(out.is_ok(),expected);if !expected{assert!(matches!(out,Err(Error::Parse)))}
 #[cfg(not(NKL_invert))] assert_eq!(log.calls,1);
 #[cfg(NKL_invert)] assert_ne!(log.calls,1);
 assert_eq!(log.offset,offset);assert_eq!(log.width,16);
}

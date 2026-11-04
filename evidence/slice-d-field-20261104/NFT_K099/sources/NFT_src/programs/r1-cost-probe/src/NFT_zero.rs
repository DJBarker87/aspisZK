use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn zero_cut(mut remaining:&[u8])->(u8,&[u8],ProgramResult){
 if !remaining.is_empty(){
  if remaining[0]!=0{return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));}
  remaining=&remaining[1..];return (2,remaining,Ok(()));
 }
 (0,remaining,Ok(()))
}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn pointer4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=4096);let view=&bytes[start..end];let(tag,rest,_)=zero_cut(view);let shift=if tag==2{1}else{0};assert!((rest.as_ptr()==view.as_ptr().wrapping_add(shift))!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn result4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=4096);let view=&bytes[start..end];let(tag,_,r)=zero_cut(view);let want=if start==end{0}else if bytes[start]!=0{1}else{2};let good=tag==want&&if tag==1{matches!(r,Err(ProgramError::AccountAlreadyInitialized))}else{r.is_ok()};assert!(good!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=4096);let view=&bytes[start..end];let(tag,rest,_)=zero_cut(view);let shift=if tag==2{1}else{0};assert!((rest.len()==end-start-shift)!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn frame4096(){let bytes:[u8;4096]=kani::any();let start:usize=kani::any();let end:usize=kani::any();let probe:usize=kani::any();kani::assume(start<=end&&end<=4096&&probe<4096);let before=bytes[probe];let _=zero_cut(&bytes[start..end]);assert!((bytes[probe]==before)!=cfg!(NFT_invert));}

#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy4096_positive(){let src:[u8;4096]=kani::any();let mut dst:[u8;4096]=kani::any();let i:usize=kani::any();kani::assume(i<4096);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[i]==dst[i]);}

#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy4096_negative(){let src:[u8;4096]=kani::any();let mut dst:[u8;4096]=kani::any();let i:usize=kani::any();kani::assume(i<4096);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[i]!=dst[i]);}

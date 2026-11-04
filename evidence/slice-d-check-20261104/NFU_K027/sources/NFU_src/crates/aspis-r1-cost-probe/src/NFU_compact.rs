use super::*;
#[kani::proof] #[kani::unwind(6)]
fn check_one(){let c:[u8;16]=kani::any();let result=check_values(&c);let valid=(0..4).all(|i|u32::from_le_bytes([c[4*i],c[4*i+1],c[4*i+2],c[4*i+3]])<0x7fffffff);assert!((result==if valid{Ok(())}else{Err(CodecError::NonCanonical)}) != cfg!(NFU_invert));}

include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Retain LPn's original property/name. KMX is now the EXACT adopted patch.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn LPn_step_frame(){
 let source:[u8;16]=kani::any();let mut backing:[u8;96]=kani::any();
 let slot:usize=kani::any();kani::assume(slot<3);let at=32*slot;
 let end:usize=kani::any();kani::assume(at+32<=end&&end<=96);
 let j:usize=kani::any();kani::assume(j<end);let old=backing[j];let base=backing.as_mut_ptr();
 let window=&mut backing[..end][at..at+32];
 let same_window=core::ptr::eq(window.as_ptr(),base.wrapping_add(at))&&window.len()==32;
 let result=expand_values(&source,window);
 let expected=if at<=j&&j<at+16{source[j-at]}else if at+16<=j&&j<at+32{0}else{old};
 assert!((same_window&&result==Ok(())&&backing[j]==expected&&core::ptr::eq(backing.as_ptr(),base)) != cfg!(NFU_invert));
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy16(){let source:[u8;16]=kani::any();let mut out:[u8;16]=kani::any();out.copy_from_slice(&source);let j:usize=kani::any();kani::assume(j<16);assert!((out[j]==source[j]) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn expand_reject(){let source:[u8;1856]=kani::any();let mut out:[u8;3712]=kani::any();let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=1856&&m<=3712);kani::assume(n%16!=0||m!=2*n);let j:usize=kani::any();kani::assume(j<3712);let old=out[j];let r=expand_values(&source[..n],&mut out[..m]);assert!((r==Err(CodecError::Length)&&out[j]==old) != cfg!(NFU_invert));}

// Arbitrary iterator pre-state; no prior decoding or whole-buffer loop.
#[kani::proof] #[kani::unwind(3)]
fn check_iterator(){let b:[u8;464]=kani::any();let i:usize=kani::any();kani::assume(i<=29);let mut it=b[16*i..].chunks_exact(16);let mut exact=it.len()==29-i&&it.remainder().is_empty();match it.next(){None=>{exact&=i==29&&it.len()==0;},Some(c)=>{exact&=i<29&&c.len()==16&&core::ptr::eq(c.as_ptr(),b[16*i..].as_ptr())&&it.len()==29-(i+1);match it.next(){None=>exact&=i+1==29,Some(next)=>exact&=i+1<29&&core::ptr::eq(next.as_ptr(),b[16*(i+1)..].as_ptr())};}}assert!(exact != cfg!(NFU_invert));}

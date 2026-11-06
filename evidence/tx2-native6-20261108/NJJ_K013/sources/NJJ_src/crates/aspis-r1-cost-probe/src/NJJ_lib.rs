use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
// rule-3 differential: one iteration of documented Iterator::any semantics.
// Arbitrary pre-state, both end and hit/miss. The receiver is the SAME iterator.
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn any_step(){
 let bytes:[u8;16]=kani::any();let at:usize=kani::any();let end:usize=kani::any();
 kani::assume(at<=end && end<=16);
 let mut it=bytes[at..end].iter();let mut calls=0usize;let mut seen=0u8;
 let out=it.by_ref().take(1).any(|b|{calls+=1;seen=*b;*b!=0});
 let entered=at<end;let expected=entered && bytes[at]!=0;
 assert_eq!(out,expected ^ cfg!(NJJ_invert));
 assert_eq!(calls,if entered{1}else{0});
 if entered{assert_eq!(seen,bytes[at]);}
 assert_eq!(it.as_slice(),&bytes[at+if entered{1}else{0}..end]);
}
// rule-3 differential: arbitrary chunk width, offset, backing and suffix.
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn chunks_step(){
 let bytes:[u8;36]=kani::any();let at:usize=kani::any();let end:usize=kani::any();let width:usize=kani::any();
 kani::assume(at<=end && end<=36 && width>0 && width<=8);
 let s=&bytes[at..end];let mut it=s.chunks_exact(width);let out=it.next();
 let entered=end-at>=width;
 assert_eq!(out.is_some(),entered ^ cfg!(NJJ_invert));
 if let Some(chunk)=out{assert_eq!(chunk,&bytes[at..at+width]);}
 let rem=(end-at)%width;
 assert_eq!(it.remainder(),&bytes[end-rem..end]);
 assert_eq!(it.len(),(end-at)/width-if entered{1}else{0});
 // One following observable window of the remaining iterator, not a full traversal.
 let next=it.next();
 if end-at>=2*width{assert_eq!(next,Some(&bytes[at+width..at+2*width]));}else{assert_eq!(next,None);}
}

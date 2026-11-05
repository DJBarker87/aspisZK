use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use aspis_core::field::{M31,CM31,QM31,WideExact};
fn wide(w:[u32;8])->WideExact{WideExact{c0:QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}},c1:QM31{c0:CM31{a:M31(w[4]),b:M31(w[5])},c1:CM31{a:M31(w[6]),b:M31(w[7])}}}}
fn words(w:WideExact)->[u32;8]{[w.c0.c0.a.0,w.c0.c0.b.0,w.c0.c1.a.0,w.c0.c1.b.0,w.c1.c0.a.0,w.c1.c0.b.0,w.c1.c1.a.0,w.c1.c1.b.0]}
struct SampleLog{count:usize,kind:u8,block:[u8;32],reply:WideExact}
fn sample(block:&[u8;32],kind:u8,l:&mut SampleLog)->WideExact{l.count+=1;l.kind=kind;l.block=*block;l.reply}
// Frozen scalar suffix, cut immediately after block returns. Sampler calls
// are local-record boundaries; trace::value is the actual frozen no-op.
fn scalar_suffix(block:[u8;32],row:u8,nonzero:bool,l:&mut SampleLog)->WideExact{
 let out=if nonzero {sample(&block,1,l)} else {sample(&block,0,l)};
 crate::trace::value(4,row as usize,out);out
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn scalar_value(){let block:[u8;32]=kani::any();let row:u8=kani::any();let mode:bool=kani::any();let old:[u32;8]=kani::any();let mut l=SampleLog{count:0,kind:99,block:kani::any(),reply:wide(old)};let out=scalar_suffix(block,row,mode,&mut l);let i:usize=kani::any();kani::assume(i<32);let j:usize=kani::any();kani::assume(j<8);assert_eq!(l.count,1);assert_eq!(l.kind,mode as u8);assert_eq!(l.block[i],block[i]);assert!((words(out)[j]==old[j])!=cfg!(NGT_invert));assert_eq!(words(l.reply)[j],old[j]);}
struct QLog{count:usize,block:[u8;32],reply:QM31}
fn qsample(block:&[u8;32],l:&mut QLog)->QM31{l.count+=1;l.block=*block;l.reply}
fn scalar_k_suffix(block:[u8;32],row:u8,l:&mut QLog)->QM31{
 let out=qsample(&block,l);crate::trace::value(4,row as usize,WideExact::from_qm31(out));out
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn scalar_k_value(){let block:[u8;32]=kani::any();let row:u8=kani::any();let w:[u32;8]=kani::any();let q=wide(w).c0;let mut l=QLog{count:0,block:kani::any(),reply:q};let out=scalar_k_suffix(block,row,&mut l);let i:usize=kani::any();kani::assume(i<32);let j:usize=kani::any();kani::assume(j<4);assert_eq!(l.count,1);assert_eq!(l.block[i],block[i]);let got=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0];assert!((got[j]==w[j])!=cfg!(NGT_invert));}
// ONE frozen add_small_base_p iteration on arbitrary mutable pre-state.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn add_digit(){let mut digits:[u32;8]=kani::any();let old=digits;let at:usize=kani::any();kani::assume(at<8);let mut addend:u32=kani::any();let before=addend;kani::assume(digits[at]<2147483647&&addend<=257);let digit=&mut digits[at];let sum=u64::from(*digit)+u64::from(addend);*digit=(sum%2147483647u64)as u32;addend=(sum/2147483647u64)as u32;let expected=u64::from(old[at])+u64::from(before);let ge=expected>=2147483647;let out=if ge{expected-2147483647}else{expected};let next=if ge{1}else{0};assert!((u64::from(digits[at])==out)!=cfg!(NGT_invert));assert_eq!(addend,next);assert!(digits[at]<2147483647&&addend<=1);let j:usize=kani::any();kani::assume(j<8);if j!=at{assert_eq!(digits[j],old[j]);}}

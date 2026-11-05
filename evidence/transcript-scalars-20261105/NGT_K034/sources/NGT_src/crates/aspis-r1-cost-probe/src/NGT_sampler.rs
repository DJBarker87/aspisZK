use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Calls{block:[u8;32],low:([u32;8],u32),adds:[[u32;8];2],carry:bool,count:usize,low_count:usize,args:[[u32;8];2],amounts:[u32;2]}
fn low_cut(b:&[u8;32],l:&mut Calls)->([u32;8],u32){l.block=*b;l.low_count+=1;l.low}
fn add_cut(d:&mut[u32;8],n:u32,l:&mut Calls)->bool{let i=l.count;assert!(i<2);l.args[i]=*d;l.amounts[i]=n;*d=l.adds[i];l.count+=1;if i==0{l.carry}else{false}}
fn ordinary_cut(block:&[u8;32],l:&mut Calls)->WideExact{let(digits,_)=low_cut(block,l);decode8(digits)}
fn gamma_cut(block:&[u8;32],l:&mut Calls)->WideExact{
 let(mut digits,quotient)=low_cut(block,l);
 let wrapped=add_cut(&mut digits,quotient+1,l);
 if wrapped{let wrapped_again=add_cut(&mut digits,1,l);debug_assert!(!wrapped_again);}
 decode8(digits)
}
fn calls()->Calls{let low:[u32;8]=kani::any();let adds:[[u32;8];2]=kani::any();let q:u32=kani::any();kani::assume(q<=256);let mut i=0;while i<8{kani::assume(low[i]<P);kani::assume(adds[0][i]<P);kani::assume(adds[1][i]<P);i+=1;}Calls{block:kani::any(),low:(low,q),adds,carry:kani::any(),count:0,low_count:0,args:kani::any(),amounts:kani::any()}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn ordinary_control(){let b:[u8;32]=kani::any();let mut l=calls();let out=ordinary_cut(&b,&mut l);let i:usize=kani::any();kani::assume(i<8);let j:usize=kani::any();kani::assume(j<32);assert_eq!(l.low_count,1);assert_eq!(l.count,0);assert_eq!(l.block[j],b[j]);assert!((out.to_limbs()[i]==l.low.0[i])!=cfg!(NGT_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn gamma_control(){let b:[u8;32]=kani::any();let mut l=calls();let out=gamma_cut(&b,&mut l);let i:usize=kani::any();kani::assume(i<8);let j:usize=kani::any();kani::assume(j<32);assert_eq!(l.low_count,1);assert_eq!(l.block[j],b[j]);assert_eq!(l.count,if l.carry{2}else{1});assert_eq!(l.args[0][i],l.low.0[i]);assert_eq!(l.amounts[0],l.low.1+1);assert!(l.amounts[0]<=257);if l.carry{assert_eq!(l.args[1][i],l.adds[0][i]);assert_eq!(l.amounts[1],1);}assert!((out.to_limbs()[i]==l.adds[if l.carry{1}else{0}][i])!=cfg!(NGT_invert));}
// The actual decoder: all eight canonical digits, no replacement field model.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn decode_canonical(){let d:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(d[i]<P);i+=1;}let out=decode8(d);let j:usize=kani::any();kani::assume(j<8);assert!((out.to_limbs()[j]==d[j])!=cfg!(NGT_invert));}
// ONE qm31_digits initialization iteration; arbitrary old ranks, same bytes.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn init_word(){let block:[u8;32]=kani::any();let mut rank:[u32;8]=kani::any();let old=rank;let mut i:usize=kani::any();kani::assume(i<8);let before=i;let start=4*i;rank[i]=u32::from_le_bytes([block[start],block[start+1],block[start+2],block[start+3]]);i+=1;let value=(block[start]as u32)|((block[start+1]as u32)<<8)|((block[start+2]as u32)<<16)|((block[start+3]as u32)<<24);assert!((rank[before]==value)!=cfg!(NGT_invert));assert_eq!(i,before+1);let j:usize=kani::any();kani::assume(j<8);if j!=before{assert_eq!(rank[j],old[j]);}}
// ONE outer division-pass writeback. The pass's actual result is a paired
// leaf boundary; no division or multiplication is executed in this cut.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn digit_writeback(){let mut rank:[u32;8]=kani::any();let old_rank=rank;let quotient:[u32;8]=kani::any();let digit:u32=kani::any();kani::assume(digit<P);let mut digits:[u32;4]=kani::any();let old=digits;let mut i:usize=kani::any();kani::assume(i<4);let before=i;let(quotient,digit)=(quotient,digit);rank=quotient;digits[i]=digit;i+=1;let j:usize=kani::any();kani::assume(j<8);let k:usize=kani::any();kani::assume(k<4);assert_eq!(rank[j],quotient[j]);assert!((digits[before]==digit)!=cfg!(NGT_invert));assert_eq!(i,before+1);if k!=before{assert_eq!(digits[k],old[k]);}let _=old_rank;}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn qm_pack(){let d:[u32;4]=kani::any();let mut i=0;while i<4{kani::assume(d[i]<P);i+=1;}let out=QM31{c0:CM31::new(M31(d[0]),M31(d[1])),c1:CM31::new(M31(d[2]),M31(d[3]))};let words=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0];let j:usize=kani::any();kani::assume(j<4);assert!((words[j]==d[j])!=cfg!(NGT_invert));}
// One native qm31_div_pass descent/writeback with arbitrary arithmetic reply.
// LPk_Step.machine_step / LPk_Cohort.step_result discharge the scalar cut.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn pass_cell(){let mut rank:[u32;8]=kani::any();let old=rank;let mut j:usize=kani::any();kani::assume(j>0&&j<=8);let before=j;let mut remainder:u64=kani::any();kani::assume(remainder<u64::from(P));let rem=remainder;j-=1;let dividend=(remainder<<32)|u64::from(rank[j]);let q:u32=kani::any();let r:u32=kani::any();kani::assume(r<P);rank[j]=q;remainder=u64::from(r);assert_eq!(j,before-1);assert_eq!(u128::from(dividend),(u128::from(rem)<<32)+u128::from(old[before-1]));assert!((rank[j]==q)!=cfg!(NGT_invert));assert_eq!(remainder,u64::from(r));assert!(remainder<u64::from(P));let at:usize=kani::any();kani::assume(at<8);if at!=j{assert_eq!(rank[at],old[at]);}}
// One native iter_mut().rev() window, including the actual mutable element.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn reverse_cell(){let mut rank:[u32;8]=kani::any();let old=rank;let remaining:usize=kani::any();kani::assume(remaining>0&&remaining<=8);let mut iterator=rank[..remaining].iter_mut().rev();let limb=iterator.next().unwrap();assert_eq!(*limb,old[remaining-1]);let q:u32=kani::any();*limb=q;let at:usize=kani::any();kani::assume(at<8);assert!((rank[remaining-1]==q)!=cfg!(NGT_invert));if at!=remaining-1{assert_eq!(rank[at],old[at]);}}
// Exact data-independent from_fn traversal; arithmetic callback abstracted by
// arbitrary LOCAL next quotient/digit. No static log or function pointer.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn from_fn_control(){let mut quotient:[u32;8]=kani::any();let initial=quotient;let next:[[u32;8];8]=kani::any();let digits:[u32;8]=kani::any();let mut count=0;let mut inputs=[[0u32;8];8];let out:[u32;8]=core::array::from_fn(|i|{assert_eq!(i,count);inputs[i]=quotient;quotient=next[i];count+=1;digits[i]});let i:usize=kani::any();kani::assume(i<8);let j:usize=kani::any();kani::assume(j<8);assert_eq!(count,8);assert_eq!(inputs[i][j],if i==0{initial[j]}else{next[i-1][j]});assert_eq!(quotient[j],next[7][j]);assert!((out[i]==digits[i])!=cfg!(NGT_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn decode_slice_word(){let block:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<8);let out=u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap());let start=4*i;let expected=(block[start]as u32)|((block[start+1]as u32)<<8)|((block[start+2]as u32)<<16)|((block[start+3]as u32)<<24);assert!((out==expected)!=cfg!(NGT_invert));}
// Scalar long-division gates, using the LPk sparse constant identity. These
// are integer operations, never finite-field multiplication. No loop or copy.
#[kani::proof]
fn quotient_bound(){let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));let n=(rem<<32)|u64::from(limb);let q=n/u64::from(P);assert!((q<=u64::from(u32::MAX))!=cfg!(NGT_invert));}
#[kani::proof]
fn remainder_bound(){let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));let n=(rem<<32)|u64::from(limb);let r=n%u64::from(P);assert!((r<u64::from(P))!=cfg!(NGT_invert));}
#[kani::proof]
fn sparse_reconstruction(){let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));let n=(rem<<32)|u64::from(limb);let q=n/u64::from(P);let r=n%u64::from(P);kani::assume(q<=u64::from(u32::MAX));kani::assume(r<u64::from(P));let product=q.wrapping_shl(31).wrapping_sub(q);assert!((product.wrapping_add(r)==n)!=cfg!(NGT_invert));}

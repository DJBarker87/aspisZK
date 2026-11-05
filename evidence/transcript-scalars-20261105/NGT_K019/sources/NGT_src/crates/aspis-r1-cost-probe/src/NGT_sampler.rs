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

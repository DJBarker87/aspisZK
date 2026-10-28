#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn KMY_expand_copy_window() {
 let source:[u8;16]=kani::any();let mut dst:[u8;96]=kani::any();
 let at:usize=kani::any();kani::assume(at<=80);
 let j:usize=kani::any();kani::assume(j<96);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[at..at+16],&source);
 assert_eq!(dst[j],if at<=j && j<at+16 {source[j-at]} else {old});
}
#[kani::proof]
#[kani::unwind(17)]
fn KMY_expand_zero_window() {
 let mut dst:[u8;96]=kani::any();let at:usize=kani::any();kani::assume(at<=80);
 let j:usize=kani::any();kani::assume(j<96);let old=dst[j];
 dst[at..at+16].fill(0);
 assert_eq!(dst[j],if at<=j && j<at+16 {0} else {old});
}

#[kani::proof]
fn KMY_expand_metadata() {
 let mut backing:[u8;96]=kani::any();let slot:usize=kani::any();kani::assume(slot<3);
 let at=32*slot;let end:usize=kani::any();kani::assume(at+32<=end && end<=96);
 let base=backing.as_mut_ptr();let window=&mut backing[..end][at..at+32];
 assert!(core::ptr::eq(window.as_ptr(),base.wrapping_add(at)));
 assert_eq!(window.len(),32);assert_eq!(16usize%16,0);assert_eq!(window.len(),2*16);
 assert!(core::ptr::eq(backing.as_ptr(),base));
}

#[path="KMY_field.rs"] mod field;
use field::{WideExact as E,QM31 as K,CM31,M31};
fn any_e()->E {let raw:[u32;8]=kani::any();for x in raw{kani::assume(x<0x7fff_ffff);}E::from_limbs(raw).unwrap()}
#[kani::proof] #[kani::unwind(33)]
fn KMY_wide_one_window() {
 let e=any_e();let raw=e.to_limbs();let src=e.to_le_bytes();
 let mut dst:[u8;64]=kani::any();let pos:usize=kani::any();kani::assume(pos<=32);
 let j:usize=kani::any();kani::assume(j<64);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+32{let b=j-pos;raw[b/4].to_le_bytes()[b%4]}else{old});
}
#[kani::proof] #[kani::unwind(5)]
fn KMY_limb_window() {
 let raw:u32=kani::any();let src=raw.to_le_bytes();let mut dst:[u8;32]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=28);let j:usize=kani::any();kani::assume(j<32);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+4],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+4{(raw>>(8*(j-pos)))as u8}else{old});
}

#[derive(Debug,PartialEq)]enum Error {Parse}
#[derive(Debug,PartialEq)]enum Variant {S2}
struct View<'a>{variant:Variant,semantic:&'a[u8],y1:&'a[u8],inactive:E,round0:&'a[u8],folded_root:Option<&'a[u8;32]>,round1:&'a[u8],final_message:&'a[u8],query_bytes:&'a[u8]}
mod compact {
 pub const OFF_INACTIVE:usize=7495;pub const OFF_ROUND0:usize=7527;
 pub const OFF_FOLDED_ROOT:usize=7751;pub const OFF_ROUND1:usize=7783;
 pub const OFF_FINAL:usize=8007;pub const OFF_OPENINGS:usize=10055;
}
fn wide_view<'a>(proof: &'a [u8], semantic: &'a [u8], y1: &'a [u8]) -> Result<View<'a>, Error> {
    Ok(View {
        variant: Variant::S2,
        semantic,
        y1,
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}

#[kani::proof] #[kani::unwind(33)]
fn KMY_view_layout_after_window(){
 let mut proof=[0u8;57607];let b:[u8;32]=kani::any();
 // Split at the completed copy; indexed writes establish the input relation.
 for j in 0..32 {proof[compact::OFF_INACTIVE+j]=b[j];}
 let semantic=[0u8;13831];let y1=[0u8;928];
 let actual=wide_view(&proof,&semantic,&y1);let inactive=E::from_le_bytes(&b);
 match (actual,inactive){
 (Err(e),None)=>assert_eq!(e,Error::Parse),
 (Ok(v),Some(x))=>{
 assert_eq!(v.inactive,x);assert_eq!(v.variant,Variant::S2);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
 },_=>assert!(false)
 }
}
#[kani::proof] #[kani::unwind(33)]
fn KMY_view_copy_window(){
 let source:[u8;32]=kani::any();let mut dst:[u8;57607]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=57575);let j:usize=kani::any();kani::assume(j<57607);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&source);
 assert_eq!(dst[j],if pos<=j && j<pos+32{source[j-pos]}else{old});
}

fn byte_window<const N:usize>() {
 let src:[u8;N]=kani::any();let mut dst:[u8;1768]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=1768-N);
 let j:usize=kani::any();kani::assume(j<1768);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+N],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+N{src[j-pos]}else{old});
}
#[kani::proof] #[kani::unwind(17)] fn KMY_checkpoint_window16(){byte_window::<16>();}
#[kani::proof] #[kani::unwind(33)] fn KMY_checkpoint_window32(){byte_window::<32>();}
#[kani::proof] #[kani::unwind(5)] fn KMY_checkpoint_window4(){byte_window::<4>();}
#[kani::proof] #[kani::unwind(67)]
fn KMY_weights_copy_window(){
 let raw:[[u32;4];64]=kani::any();
 let src=raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}});
 let mut dst:[K;66]=core::array::from_fn(|_|{let r:[u32;4]=kani::any();K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}});
 let pos:usize=kani::any();kani::assume(pos<=2);let j:usize=kani::any();kani::assume(j<66);
 let old=dst[j];KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+64],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+64{src[j-pos]}else{old});
}
#[kani::proof] #[kani::unwind(17)]
fn KMY_scalar_one_window(){
 let raw:[u32;4]=kani::any();let k=K{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};
 let mut src=[0u8;16];k.write_le_bytes(&mut src);
 let mut dst:[u8;48]=kani::any();let pos:usize=kani::any();kani::assume(pos<=32);
 let j:usize=kani::any();kani::assume(j<48);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+16],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+16{let b=j-pos;raw[b/4].to_le_bytes()[b%4]}else{old});
}

#[kani::proof] #[kani::unwind(33)]
fn KMY_local_window32(){
 let src:[u8;32]=kani::any();let mut dst:[u8;64]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=32);let j:usize=kani::any();kani::assume(j<64);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+32{src[j-pos]}else{old});
}
#[kani::proof] #[kani::unwind(33)]
fn KMY_view_accept_layout(){
 let e=any_e();let b=e.to_le_bytes();let mut proof=[0u8;57607];
 for j in 0..32 {proof[compact::OFF_INACTIVE+j]=b[j];}
 let semantic=[0u8;13831];let y1=[0u8;928];let v=wide_view(&proof,&semantic,&y1).unwrap();
 assert_eq!(v.inactive,e);assert_eq!(v.variant,Variant::S2);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
}
fn view_reject<const BAD:usize>(){
 let mut raw:[u32;8]=kani::any();kani::assume(raw[BAD]>=0x7fff_ffff);
 let mut proof=[0u8;57607];for limb in 0..8{for byte in 0..4{proof[compact::OFF_INACTIVE+4*limb+byte]=raw[limb].to_le_bytes()[byte];}}
 assert!(matches!(wide_view(&proof,&[],&[]),Err(Error::Parse)));
}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject0(){view_reject::<0>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject1(){view_reject::<1>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject2(){view_reject::<2>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject3(){view_reject::<3>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject4(){view_reject::<4>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject5(){view_reject::<5>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject6(){view_reject::<6>();}
#[kani::proof] #[kani::unwind(9)] fn KMY_view_reject7(){view_reject::<7>();}
#[kani::proof] #[kani::unwind(193)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMY_wide_append_one(){
 let initial:[u8;160]=kani::any();let slot:usize=kani::any();kani::assume(slot<6);let len=32*slot;
 let e=any_e();let raw=e.to_limbs();let encoded=e.to_le_bytes();
 let mut out=KMX_stubs::KMX_to_vec(&initial[..len]);
 KMX_stubs::KMX_extend_from_slice(&mut out,&encoded);
 assert_eq!(out.len(),len+32);let j:usize=kani::any();kani::assume(j<out.len());
 assert_eq!(out[j],if j<len{initial[j]}else{let b=j-len;raw[b/4].to_le_bytes()[b%4]});
}
#[kani::proof] #[kani::unwind(33)]
fn KMY_parse_accept(){
 let e=any_e();let encoded=e.to_le_bytes();let mut local=[0u8;32];
 KMX_stubs::KMX_copy_from_slice(&mut local,&encoded);
 assert_eq!(E::from_le_bytes(&local),Some(e));
}
#[kani::proof] #[kani::unwind(9)]
fn KMY_view_metadata_zero(){
 let proof=[0u8;57607];let semantic=[0u8;13831];let y1=[0u8;928];
 let v=wide_view(&proof,&semantic,&y1).unwrap();
 assert_eq!(v.variant,Variant::S2);assert_eq!(v.inactive,E::ZERO);
 assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr()));assert_eq!(v.semantic.len(),semantic.len());
 assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr()));assert_eq!(v.y1.len(),y1.len());
 assert!(core::ptr::eq(v.round0.as_ptr(),proof[compact::OFF_ROUND0..].as_ptr()));assert_eq!(v.round0.len(),224);
 assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[compact::OFF_FOLDED_ROOT..].as_ptr()));
 assert!(core::ptr::eq(v.round1.as_ptr(),proof[compact::OFF_ROUND1..].as_ptr()));assert_eq!(v.round1.len(),224);
 assert!(core::ptr::eq(v.final_message.as_ptr(),proof[compact::OFF_FINAL..].as_ptr()));assert_eq!(v.final_message.len(),2048);
 assert_eq!(v.query_bytes.len(),0);
}

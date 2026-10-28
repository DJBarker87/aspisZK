use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
static mut NCH_PROOF:*const u8=core::ptr::null();
static mut NCH_PASS:bool=false;
static mut NCH_STAGE:u8=0;
fn NCH_check(bytes:&[u8])->Result<(),CodecError>{unsafe{
 assert_eq!(NCH_STAGE,0,"check first");assert_eq!(bytes.as_ptr(),NCH_PROOF.add(compact::OFF_Y1),"same y1 pointer");
 assert_eq!(bytes.len(),compact::OFF_INACTIVE-compact::OFF_Y1,"same y1 length");NCH_STAGE=1;
 if NCH_PASS {Ok(())}else{Err(CodecError::NonCanonical)}
}}
fn NCH_tail(bytes:&[u8],k:bool)->Result<(),Error>{unsafe{
 assert!(NCH_PASS,"reached only after check success");assert_eq!(NCH_STAGE,1,"no intervening tail");
 assert_eq!(bytes.as_ptr(),NCH_PROOF.add(compact::OFF_INACTIVE));assert_eq!(bytes.len(),32);assert!(!k);
 kani::cover!(true,"first wide check reached after SAME compact success");kani::assume(false);Err(Error::Parse)
}}
#[kani::proof]#[kani::unwind(2)]
#[kani::stub(crate::compact::check_values,NCH_check)]
#[kani::stub(crate::verifier::echeck,NCH_tail)]
fn NCH_scan_prefix(){
 let proof:[u8;57607]=kani::any();unsafe{NCH_PROOF=proof.as_ptr();NCH_PASS=kani::any();NCH_STAGE=0;}
 let r=canonical_scan(&proof);assert_eq!(r,Err(Error::Parse));unsafe{assert!(!NCH_PASS);assert_eq!(NCH_STAGE,1);}
}
#[kani::proof]#[kani::unwind(2)]
#[kani::stub(crate::compact::check_values,NCH_check)]
#[kani::stub(crate::verifier::echeck,NCH_tail)]
fn NCH_scan_error_wrong(){
 let proof:[u8;57607]=kani::any();unsafe{NCH_PROOF=proof.as_ptr();NCH_PASS=false;NCH_STAGE=0;}
 assert!(canonical_scan(&proof).is_ok(),"forced compact error cannot accept");
}
fn NCH_check_wrong(bytes:&[u8])->Result<(),CodecError>{unsafe{assert_eq!(bytes.as_ptr(),NCH_PROOF.add(compact::OFF_Y1+1),"wrong y1 offset");}Err(CodecError::NonCanonical)}
#[kani::proof]#[kani::unwind(2)]
#[kani::stub(crate::compact::check_values,NCH_check_wrong)]
fn NCH_scan_pointer_wrong(){let proof:[u8;57607]=kani::any();unsafe{NCH_PROOF=proof.as_ptr();}let _=canonical_scan(&proof);}
#[kani::requires(src.len()==32 && dst.len()==32 && j<32)]
#[kani::modifies(dst)]
#[kani::ensures(|_| dst[j]==src[j])]
fn NCH_copy32(src:&[u8],dst:&mut[u8],j:usize){dst.copy_from_slice(src);}
#[kani::proof_for_contract(NCH_copy32)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_contract32(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_copy32(&src,&mut dst,j);}
#[kani::requires(src.len()==32 && dst.len()==32 && j<32)]
#[kani::modifies(dst)]
#[kani::ensures(|_| dst[j]!=src[j])]
fn NCH_invert32(src:&[u8],dst:&mut[u8],j:usize){dst.copy_from_slice(src);}
#[kani::proof_for_contract(NCH_invert32)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_inverted32(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_invert32(&src,&mut dst,j);}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub_verified(NCH_copy32)]
fn NCH_unimplied32(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();NCH_copy32(&src,&mut dst,0);assert_eq!(dst[31],src[31],"contract says only byte0");}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_real32(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();NCH_copy32(&src,&mut dst,0);assert_eq!(dst[31],src[31]);}
#[kani::requires(src.len()==32 && dst.len()==32 && j<32)]
#[kani::modifies(&mut dst[..16])]
#[kani::ensures(|_| dst[j]==src[j])]
fn NCH_badframe32(src:&[u8],dst:&mut[u8],j:usize){dst.copy_from_slice(src);}
#[kani::proof_for_contract(NCH_badframe32)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_modifies32(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_badframe32(&src,&mut dst,j);}
#[kani::proof]#[kani::unwind(2)]
#[kani::stub_verified(NCH_copy32)]
fn NCH_root_frame_contract(){
 let input:[u8;7015]=kani::any();let mut logical:[u8;14759]=kani::any();let j:usize=kani::any();kani::assume(j>=32&&j<14759);let old=logical[j];
 NCH_copy32(&input[..32],&mut logical[..32],0);assert_eq!(logical[j],old);kani::cover!(j==14758,"same y1 suffix");
}
// Array carrier isolates the unsized-slice modifies reachability failure.
#[kani::requires(j<32)]
#[kani::modifies(dst)]
#[kani::ensures(|_| dst[j]==src[j])]
fn NCH_arraycopy(src:&[u8;32],dst:&mut[u8;32],j:usize){dst.as_mut_slice().copy_from_slice(src.as_slice());}
#[kani::proof_for_contract(NCH_arraycopy)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_array_contract(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_arraycopy(&src,&mut dst,j);}
#[kani::proof]#[kani::unwind(35)]#[kani::stub_verified(NCH_arraycopy)]
fn NCH_array_unimplied(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();NCH_arraycopy(&src,&mut dst,0);assert_eq!(dst[31],src[31],"contract says only byte0");}
#[kani::requires(j<32)]#[kani::modifies(dst)]#[kani::ensures(|_| dst[j]!=src[j])]
fn NCH_arrayinvert(src:&[u8;32],dst:&mut[u8;32],j:usize){dst.as_mut_slice().copy_from_slice(src.as_slice());}
#[kani::proof_for_contract(NCH_arrayinvert)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_array_inverted(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_arrayinvert(&src,&mut dst,j);}
#[kani::requires(j<32)]#[kani::modifies(&mut dst[..16])]#[kani::ensures(|_| dst[j]==src[j])]
fn NCH_arraybadframe(src:&[u8;32],dst:&mut[u8;32],j:usize){dst.as_mut_slice().copy_from_slice(src.as_slice());}
#[kani::proof_for_contract(NCH_arraybadframe)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_array_modifies(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_arraybadframe(&src,&mut dst,j);}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_array_real(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();NCH_arraycopy(&src,&mut dst,0);assert_eq!(dst[31],src[31]);}
#[kani::proof]#[kani::unwind(2)]#[kani::stub_verified(NCH_arraycopy)]
fn NCH_array_root_frame(){let src:[u8;7015]=kani::any();let mut dst:[u8;14759]=kani::any();let j:usize=kani::any();kani::assume(32<=j&&j<14759);let old=dst[j];
 let s:&[u8;32]=(&src[..32]).try_into().unwrap();let d:&mut[u8;32]=(&mut dst[..32]).try_into().unwrap();NCH_arraycopy(s,d,0);assert_eq!(dst[j],old);}
#[kani::proof]#[kani::unwind(2)]#[kani::stub_verified(NCH_arraycopy)]
fn NCH_array_root_wrong(){let src:[u8;7015]=kani::any();let mut dst:[u8;14759]=kani::any();let old=dst[14758];
 let s:&[u8;32]=(&src[..32]).try_into().unwrap();let d:&mut[u8;32]=(&mut dst[..32]).try_into().unwrap();NCH_arraycopy(s,d,0);assert_ne!(dst[14758],old,"negative exterior law");}
#[kani::proof]#[kani::unwind(2)]#[kani::stub_verified(NCH_arraycopy)]
fn NCH_array_root_value(){let src:[u8;7015]=kani::any();let mut dst:[u8;14759]=kani::any();let j:usize=kani::any();kani::assume(j<32);
 NCH_arraycopy((&src[..32]).try_into().unwrap(),(&mut dst[..32]).try_into().unwrap(),j);assert_eq!(dst[j],src[j]);}
#[kani::proof]#[kani::unwind(2)]#[kani::stub_verified(NCH_arraycopy)]
fn NCH_array_root_value_wrong(){let mut src:[u8;7015]=kani::any();let mut dst:[u8;14759]=kani::any();src[31]=1;
 NCH_arraycopy((&src[..32]).try_into().unwrap(),(&mut dst[..32]).try_into().unwrap(),31);assert_eq!(dst[31],0,"negative root output");}
#[kani::requires(j<5)]#[kani::modifies(dst)]#[kani::ensures(|_| dst[j]==src[j])]
fn NCH_headercopy(src:&[u8;5],dst:&mut[u8;5],j:usize){dst.as_mut_slice().copy_from_slice(src.as_slice());}
#[kani::proof_for_contract(NCH_headercopy)]#[kani::unwind(8)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_header_contract(){let src:[u8;5]=kani::any();let mut dst:[u8;5]=kani::any();let j:usize=kani::any();NCH_headercopy(&src,&mut dst,j);}
#[kani::requires(j<5)]#[kani::modifies(dst)]#[kani::ensures(|_| dst[j]!=src[j])]
fn NCH_headerinvert(src:&[u8;5],dst:&mut[u8;5],j:usize){dst.as_mut_slice().copy_from_slice(src.as_slice());}
#[kani::proof_for_contract(NCH_headerinvert)]#[kani::unwind(8)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_header_inverted(){let src:[u8;5]=kani::any();let mut dst:[u8;5]=kani::any();let j:usize=kani::any();NCH_headerinvert(&src,&mut dst,j);}
#[kani::proof]#[kani::unwind(8)]#[kani::stub_verified(NCH_headercopy)]
fn NCH_header_unimplied(){let src:[u8;5]=kani::any();let mut dst:[u8;5]=kani::any();NCH_headercopy(&src,&mut dst,0);assert_eq!(dst[4],src[4]);}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_header_real(){let src:[u8;5]=kani::any();let mut dst:[u8;5]=kani::any();NCH_headercopy(&src,&mut dst,0);assert_eq!(dst[4],src[4]);}
#[kani::requires(j<5)]#[kani::modifies(&mut dst[..4])]#[kani::ensures(|_| dst[j]==src[j])]
fn NCH_headerbadframe(src:&[u8;5],dst:&mut[u8;5],j:usize){dst.as_mut_slice().copy_from_slice(src.as_slice());}
#[kani::proof_for_contract(NCH_headerbadframe)]#[kani::unwind(8)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_header_modifies(){let src:[u8;5]=kani::any();let mut dst:[u8;5]=kani::any();let j:usize=kani::any();NCH_headerbadframe(&src,&mut dst,j);}
fn NCH_geometry(row:u8)->(usize,usize){let r=row as usize;
 let s=if r<=2 {32+5*r}else if r<=14{64+5*r}else if r<=25{155+453*(r-15)}else{6546};
 let d=if r<=2 {32+5*r}else if r<=14{64+5*r}else if r<=25{171+901*(r-15)}else{12898};(s,d)}
#[kani::proof]#[kani::unwind(2)]#[kani::stub_verified(NCH_headercopy)]
fn NCH_header_full_frame(){let src:[u8;7015]=kani::any();let mut dst:[u8;14759]=kani::any();let row:u8=kani::any();kani::assume(row<27);let(s,d)=NCH_geometry(row);let j:usize=kani::any();kani::assume(j<14759&&(j<d||j>=d+5));let old=dst[j];
 NCH_headercopy((&src[s..s+5]).try_into().unwrap(),(&mut dst[d..d+5]).try_into().unwrap(),0);assert_eq!(dst[j],old);}
#[kani::proof]#[kani::unwind(2)]#[kani::stub_verified(NCH_headercopy)]
fn NCH_header_full_wrong(){let src:[u8;7015]=kani::any();let mut dst:[u8;14759]=kani::any();let row:u8=kani::any();kani::assume(row<27);let(s,d)=NCH_geometry(row);let old=dst[14758];
 NCH_headercopy((&src[s..s+5]).try_into().unwrap(),(&mut dst[d..d+5]).try_into().unwrap(),0);assert_ne!(dst[14758],old,"negative full exterior");}
#[kani::requires(j<32)]#[kani::modifies(dst)]#[kani::ensures(|_| dst[j]==if j<16{src[j]}else{0})]
fn NCH_expandcell(src:&[u8;16],dst:&mut[u8;32],j:usize){assert!(compact::expand_values(src,dst).is_ok());}
#[kani::proof_for_contract(NCH_expandcell)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_cell_contract(){let src:[u8;16]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_expandcell(&src,&mut dst,j);}
#[kani::requires(j<32)]#[kani::modifies(dst)]#[kani::ensures(|_| dst[j]!=if j<16{src[j]}else{0})]
fn NCH_cellinvert(src:&[u8;16],dst:&mut[u8;32],j:usize){assert!(compact::expand_values(src,dst).is_ok());}
#[kani::proof_for_contract(NCH_cellinvert)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_cell_inverted(){let src:[u8;16]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_cellinvert(&src,&mut dst,j);}
#[kani::proof]#[kani::unwind(35)]#[kani::stub_verified(NCH_expandcell)]
fn NCH_cell_unimplied(){let src:[u8;16]=kani::any();let mut dst:[u8;32]=kani::any();NCH_expandcell(&src,&mut dst,0);assert_eq!(dst[31],0);}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_cell_real(){let src:[u8;16]=kani::any();let mut dst:[u8;32]=kani::any();NCH_expandcell(&src,&mut dst,0);assert_eq!(dst[31],0);}
#[kani::requires(j<32)]#[kani::modifies(&mut dst[..16])]#[kani::ensures(|_| dst[j]==if j<16{src[j]}else{0})]
fn NCH_cellbadframe(src:&[u8;16],dst:&mut[u8;32],j:usize){assert!(compact::expand_values(src,dst).is_ok());}
#[kani::proof_for_contract(NCH_cellbadframe)]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_cell_modifies(){let src:[u8;16]=kani::any();let mut dst:[u8;32]=kani::any();let j:usize=kani::any();NCH_cellbadframe(&src,&mut dst,j);}

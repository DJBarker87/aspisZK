use super::*;
fn NMX_assign_post(r:&Result<(),ProgramError>,node:&[M31;8],window:&[u8;32],j:usize,old_j:u32)->bool {
    match R::digest(window,0) {
        Err(())=>matches!(r,Err(ProgramError::InvalidAccountData)) && node[j].0==old_j,
        Ok(row)=>r.is_ok() && node[j].0==row[j],
    }
}
// Source lines497-502, after the proven 32-byte window/cast cut.
#[kani::requires(j<8 && node[j].0==before_j)]
#[cfg_attr(nnj_empty_modifies, kani::modifies())]
#[cfg_attr(not(nnj_empty_modifies), kani::modifies(node))]
#[kani::ensures(|r:&Result<(),ProgramError>| NMX_assign_post(r,node,window,j,before_j) != INVERSE)]
fn NMX_assign(node:&mut [M31;8],window:&[u8;32],j:usize,before_j:u32)->Result<(),ProgramError>{
    *node = decode_digest_canonical(
        window,
    ).map_err(|_| ProgramError::InvalidAccountData)?;
    Ok(())
}
#[kani::proof_for_contract(NMX_assign)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_assign_contract(){
    let raw:[u32;8]=kani::any();let mut node=raw.map(M31);
    let window:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<8);
    let before_j=node[j].0;let _=NMX_assign(&mut node,&window,j,before_j);
}
// Same contract and actual assignment; other output cells are not specified.
#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NNJ_assign_real() {
 let raw:[u32;8]=kani::any();let mut node=raw.map(M31);
 let window=[0u8;32];let j:usize=0; // isolate a legal index after K009 timeout
 let before_j=node[j].0;let r=NMX_assign(&mut node,&window,j,before_j);
 assert!(r.is_ok() && node[(j+1)%8].0==0,"NNJ unimplied other digest cell");
}
#[kani::proof]
#[kani::stub_verified(NMX_assign)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NNJ_assign_stub() {
 let raw:[u32;8]=kani::any();let mut node=raw.map(M31);
 let window=[0u8;32];let j:usize=0; // isolate a legal index after K009 timeout
 let before_j=node[j].0;let r=NMX_assign(&mut node,&window,j,before_j);
 assert!(r.is_ok() && node[(j+1)%8].0==0,"NNJ unimplied other digest cell");
}

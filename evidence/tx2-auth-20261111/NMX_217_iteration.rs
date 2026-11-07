use super::*;
fn NMX_assign_post(r:&Result<(),ProgramError>,node:&[M31;8],window:&[u8;32],j:usize,old_j:u32)->bool {
    match R::digest(window,0) {
        Err(())=>matches!(r,Err(ProgramError::InvalidAccountData)) && node[j].0==old_j,
        Ok(row)=>r.is_ok() && node[j].0==row[j],
    }
}
// Source lines497-502, after the proven 32-byte window/cast cut.
#[kani::requires(j<8 && node[j].0==before_j)]
#[kani::modifies(node)]
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
fn NMX_guard_post(node:&[M31;8],next_leaf_index:u64,level:usize)->bool{
    let raw=[node[0].0,node[1].0,node[2].0,node[3].0,node[4].0,node[5].0,node[6].0,node[7].0];
    (next_leaf_index>>level)&1==0 && !R::eq_digest(&raw,&R::EMPTY[level])
}
// Source line503, separated from writes to retire the combined K013/K014 shape.
#[kani::requires(level<20 && next_leaf_index<=1048576)]
#[kani::modifies()]
#[kani::ensures(|r:&bool| (*r==NMX_guard_post(node,next_leaf_index,level)) != INVERSE)]
fn NMX_guard(node:&[M31;8],next_leaf_index:u64,level:usize)->bool{
    use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
    (next_leaf_index >> level) & 1 == 0 && *node != V7_PAIR_EMPTY_ROOTS[level]
}
#[kani::proof_for_contract(NMX_guard)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_guard_contract(){
    let raw:[u32;8]=kani::any();let node=raw.map(M31);
    let next_leaf_index:u64=kani::any();let level:usize=kani::any();
    kani::assume(level<20 && next_leaf_index<=1048576);
    let _=NMX_guard(&node,next_leaf_index,level);
}
// Frozen line468, with the owned array supplied by a shared view at the cut.
#[kani::modifies()]
#[kani::ensures(|r:&bool| (*r==R::zero(master)) != INVERSE)]
fn NMX_master_zero(master:&[u8;32])->bool{*master == [0u8;32]}
#[kani::proof_for_contract(NMX_master_zero)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_master_zero_contract(){let master:[u8;32]=kani::any();let _=NMX_master_zero(&master);}

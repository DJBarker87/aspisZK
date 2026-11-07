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

// Complete frozen entry-to-first-digest segment. The borrowed prefix contains
// exactly original bytes[0..128]; logical_len is the original slice metadata.
struct NMX_prefix_state { master:[u8;32], lane:u8, bump:u8, next:u64, root_window:[u8;32] }
fn NMX_prefix_observe(p:&NMX_prefix_state,j:usize)->u64 {
 match j {0=>p.lane as u64,1=>p.bump as u64,2=>p.next,
  3..=34=>p.master[j-3] as u64,_=>p.root_window[j-35] as u64}
}
fn NMX_prefix_reference(b:&[u8;128],n:usize)->Option<NMX_prefix_state>{
 if n!=768{return None}
 if !R::equal(&b[..4],b"ASL8")||b[4]!=2||b[5]>=8||b[6]!=8||b[7]!=20||!R::equal(&b[8..40],&R::BINDING)||!R::zero(&b[73..80]){return None}
 let master=R::bytes32(b,40);if R::zero(&master){return None}
 let t=&b[80..];if !R::equal(&t[..4],b"ASPT")||t[4]!=1||t[5]!=20||t[6]!=3||t[7]!=1{return None}
 let next=R::word64(t,8);if next>1048576{return None}
 Some(NMX_prefix_state{master,lane:b[5],bump:b[72],next,root_window:R::bytes32(t,16)})
}
fn NMX_prefix_post(r:bool)->bool {r != INVERSE}
#[kani::requires(j<67)]
#[kani::modifies()]
#[kani::ensures(|r:&bool| NMX_prefix_post(*r))]
fn NMX_prefix(bytes:&[u8;128],logical_len:usize,j:usize)->bool {
 let actual:Result<NMX_prefix_state,ProgramError>=(||{
    if logical_len != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES
        || bytes[..4] != POOL_V1_PAIR_FOREST_LANE_MAGIC
        || bytes[4] != POOL_V1_PAIR_FOREST_LANE_VERSION
        || usize::from(bytes[5]) >= POOL_V1_PAIR_FOREST_LANE_COUNT
        || bytes[6] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8
        || bytes[7] != POOL_V1_PAIR_TREE_DEPTH as u8
        || bytes[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING
        || bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
            .iter()
            .any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let master: [u8; 32] = bytes[40..72]
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if master == [0u8; 32] {
        return Err(ProgramError::InvalidAccountData);
    }
    let tree = &bytes[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];
    if tree[..4] != POOL_V1_TREE_STATE_MAGIC
        || tree[4] != POOL_V1_TREE_STATE_VERSION
        || tree[5] != POOL_V1_PAIR_TREE_DEPTH as u8
        || tree[6] != POOL_V1_TREE_HASH_VERSION
        || tree[7] != POOL_V1_DIGEST_ENCODING_VERSION
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let next_leaf_index = u64::from_le_bytes(
        tree[8..16]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    );
    if next_leaf_index > POOL_V1_PAIR_CAPACITY {
        return Err(ProgramError::InvalidAccountData);
    }

    let root_window:[u8;32]=tree[16..48].try_into().map_err(|_|ProgramError::InvalidAccountData)?;
    Ok(NMX_prefix_state{master,lane:bytes[5],bump:bytes[72],next:next_leaf_index,root_window})
 })();
 match (actual,NMX_prefix_reference(bytes,logical_len)) {
  (Err(ProgramError::InvalidAccountData),None)=>true,
  (Ok(a),Some(b))=>NMX_prefix_observe(&a,j)==NMX_prefix_observe(&b,j),
  _=>false,
 }
}
#[kani::proof_for_contract(NMX_prefix)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_prefix_contract(){let bytes:[u8;128]=kani::any();let logical_len:usize=kani::any();let j:usize=kani::any();kani::assume(j<67);let _=NMX_prefix(&bytes,logical_len,j);}

fn NMX_lane_observe(a:&PoolV1PairForestLaneStateV1,j:usize)->u64{
 match j{0=>a.bump as u64,1=>a.lane_id as u64,2=>a.tree.next_leaf_index,
  3..=34=>a.master[j-3] as u64,35..=42=>a.tree.root[j-35].0 as u64,
  _=>a.tree.frontier[(j-43)/8][(j-43)%8].0 as u64}
}
fn NMX_final_post(r:bool)->bool{r != INVERSE}
#[kani::requires(j<203)]
#[kani::modifies()]
#[kani::ensures(|r:&bool| NMX_final_post(*r))]
fn NMX_final(bump:u8,master:[u8;32],lane_id:u8,next_leaf_index:u64,
 root:[M31;8],frontier:[[M31;8];20],j:usize)->bool{
 use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
 let actual:Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>=(||{
    if next_leaf_index == 0 && root != V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH] {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(Box::new(PoolV1PairForestLaneStateV1 {
        bump: bump,
        master,
        lane_id: lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index,
            root,
            frontier,
        },
    }))
 })();
 let row=root.map(|x|x.0);
 let rejected=next_leaf_index==0&&!R::eq_digest(&row,&R::EMPTY[20]);
 let expected=match j{0=>bump as u64,1=>lane_id as u64,2=>next_leaf_index,
 3..=34=>master[j-3] as u64,35..=42=>root[j-35].0 as u64,
 _=>frontier[(j-43)/8][(j-43)%8].0 as u64};
 match actual{Err(e)=>rejected&&matches!(e,ProgramError::InvalidAccountData),
 Ok(a)=>!rejected&&NMX_lane_observe(&a,j)==expected}
}
#[kani::proof_for_contract(NMX_final)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_final_contract(){let j:usize=kani::any();kani::assume(j<203);let _=NMX_final(kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),j);}

#[kani::modifies()]
#[kani::ensures(|r:&bool| (*r == !R::zero(bytes)) != INVERSE)]
fn NMX_reserved(bytes:&[u8;7])->bool {bytes.iter().any(|byte|*byte != 0)}
#[kani::proof_for_contract(NMX_reserved)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_reserved_contract(){let bytes:[u8;7]=kani::any();let _=NMX_reserved(&bytes);}

#[kani::modifies()]
#[kani::ensures(|r:&bool| *r != INVERSE)]
fn NMX_construct(input:&PoolV1PairForestLaneStateV1)->bool{
 let output =
    Box::new(PoolV1PairForestLaneStateV1 {
        bump: input.bump,
        master: input.master,
        lane_id: input.lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: input.tree.next_leaf_index,
            root: input.tree.root,
            frontier: input.tree.frontier,
        },
    });
 *output==*input
}
#[kani::proof_for_contract(NMX_construct)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NMX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NMX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NMX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NMX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NMX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NMX_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NMX_construct_contract(){
 let input=PoolV1PairForestLaneStateV1{bump:kani::any(),master:kani::any(),lane_id:kani::any(),tree:IncrementalMerkleTreeV1{next_leaf_index:kani::any(),root:kani::any(),frontier:kani::any()}};
 let _=NMX_construct(&input);
}

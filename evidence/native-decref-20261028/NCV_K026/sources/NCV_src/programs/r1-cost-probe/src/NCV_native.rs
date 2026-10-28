#![allow(non_snake_case,dead_code)]
use super::*;
use crate::NCV_reference as R;
pub fn domain_master(b:&[u8])->bool {b.len()==384 && b[4]==0}
pub fn domain_checkpoint(b:&[u8])->bool {b.len()==192 && b[4]==0}
pub fn domain_lane(b:&[u8])->bool {b.len()==768 && b[4]==0}
pub fn matches_master(a:&Result<Box<PoolV1PairForestMasterV1>,ProgramError>,b:Result<Box<R::Master>,()>)->bool{
 match(a,b){(Err(e),Err(()))=>*e==ProgramError::InvalidAccountData,(Ok(a),Ok(b))=>{
 let v=R::Master{bump:a.bump,identity:R::Identity{pool:a.identity.pool,asset_mint:a.identity.asset_mint,token_program:a.identity.token_program,asset_id:a.identity.asset_id.0,deployment_domain:a.identity.deployment_domain},verifier_policy:R::Policy{flags:a.verifier_policy.flags,registry_program:a.verifier_policy.registry_program,registry_authority:a.verifier_policy.registry_authority,policy_binding:a.verifier_policy.policy_binding},initialized_lane_mask:a.initialized_lane_mask,has_checkpoint:a.has_checkpoint,next_checkpoint_sequence:a.next_checkpoint_sequence,last_checkpoint_lane_sequences:a.last_checkpoint_lane_sequences};v==*b},_=>false}
}
pub fn matches_checkpoint(a:&Result<Box<PoolV1PairForestCheckpointV1>,ProgramError>,b:Result<Box<R::Checkpoint>,()>)->bool{
 match(a,b){(Err(e),Err(()))=>*e==ProgramError::InvalidAccountData,(Ok(a),Ok(b))=>{let mut root=[0u32;8];let mut i=0;while i<8{root[i]=a.global_root[i].0;i+=1;}
 R::Checkpoint{bump:a.bump,master:a.master,deployment_domain:a.deployment_domain,checkpoint_sequence:a.checkpoint_sequence,global_root:root,lane_sequences:a.lane_sequences}==*b},_=>false}
}
pub fn matches_lane(a:&Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>,b:Result<Box<R::Lane>,()>)->bool{
 match(a,b){(Err(e),Err(()))=>*e==ProgramError::InvalidAccountData,(Ok(a),Ok(b))=>{let mut root=[0u32;8];let mut f=[[0u32;8];20];let mut i=0;while i<8{root[i]=a.tree.root[i].0;i+=1;}let mut j=0;while j<20{let mut k=0;while k<8{f[j][k]=a.tree.frontier[j][k].0;k+=1;}j+=1;}
 R::Lane{bump:a.bump,master:a.master,lane_id:a.lane_id,next_leaf_index:a.tree.next_leaf_index,root,frontier:f}==*b},_=>false}
}
#[kani::proof_for_contract(super::decode_master_box)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NCV_master_contract(){let mut b:[u8;384]=kani::any();b[4]=0;let _=super::decode_master_box(&b);}
#[kani::proof_for_contract(super::decode_checkpoint_box)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NCV_checkpoint_contract(){let mut b:[u8;192]=kani::any();b[4]=0;let _=super::decode_checkpoint_box(&b);}
#[kani::proof_for_contract(super::decode_lane_from_pool_release)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NCV_lane_contract(){let mut b:[u8;768]=kani::any();b[4]=0;let _=super::decode_lane_from_pool_release(&b);}
#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(18)]
fn NCV_copy_positive(){let s:[u8;16]=kani::any();let mut d=[0u8;16];d.copy_from_slice(&s);let k:usize=kani::any();kani::assume(k<16);assert_eq!(d[k],s[k]);}
#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(18)]
fn NCV_copy_negative(){let s=[1u8;16];let mut d=[0u8;16];d.copy_from_slice(&s);assert_eq!(d[15],0);}

#[path="NCV_fragments.rs"] mod NCV_fragments;

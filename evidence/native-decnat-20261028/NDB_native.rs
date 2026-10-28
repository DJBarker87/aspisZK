#![allow(non_snake_case,dead_code,unused_mut)]
use super::*;
use crate::NDB_reference as R;
const NDB_INVERSE:bool=false;
fn NDB_any_identity()->aspis_statement::pool_v1::PoolIdentityV1{aspis_statement::pool_v1::PoolIdentityV1{pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:M31(kani::any()),deployment_domain:kani::any()}}
fn NDB_any_policy()->aspis_statement::pool_v1::VerifierPolicyV1{aspis_statement::pool_v1::VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()}}
fn NDB_any_master()->PoolV1PairForestMasterV1{PoolV1PairForestMasterV1{bump:kani::any(),identity:NDB_any_identity(),verifier_policy:NDB_any_policy(),initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()}}
fn NDB_any_checkpoint()->PoolV1PairForestCheckpointV1{PoolV1PairForestCheckpointV1{bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),checkpoint_sequence:kani::any(),global_root:kani::any::<[u32;8]>().map(M31),lane_sequences:kani::any()}}
fn NDB_any_lane()->PoolV1PairForestLaneStateV1{PoolV1PairForestLaneStateV1{bump:kani::any(),master:kani::any(),lane_id:kani::any(),tree:IncrementalMerkleTreeV1{next_leaf_index:kani::any(),root:kani::any::<[u32;8]>().map(M31),frontier:kani::any::<[[u32;8];20]>().map(|r|r.map(M31))}}}
#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_copy_fidelity(){let s:[u8;16]=kani::any();let mut d=[0u8;16];d.copy_from_slice(&s);let j:usize=kani::any();kani::assume(j<16);let law=d[j]==s[j];assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_policy_decoder(){let b:[u8;104]=kani::any();let actual=aspis_statement::pool_v1::decode_verifier_policy_v1(&b).map(|p|R::Policy{flags:p.flags,registry_program:p.registry_program,registry_authority:p.registry_authority,policy_binding:p.policy_binding}).map_err(|_|());let law=actual==R::policy(&b);assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_canonical_digest(){let b:[u8;32]=kani::any();let a=aspis_statement::decode_digest_canonical(&b);let w:[u32;8]=[R::word32(&b,0),R::word32(&b,4),R::word32(&b,8),R::word32(&b,12),R::word32(&b,16),R::word32(&b,20),R::word32(&b,24),R::word32(&b,28)];let canonical=w[0]<2147483647&&w[1]<2147483647&&w[2]<2147483647&&w[3]<2147483647&&w[4]<2147483647&&w[5]<2147483647&&w[6]<2147483647&&w[7]<2147483647;let law=match a{Err(_)=>!canonical,Ok(d)=>canonical&&d[0].0==w[0]&&d[1].0==w[1]&&d[2].0==w[2]&&d[3].0==w[3]&&d[4].0==w[4]&&d[5].0==w[5]&&d[6].0==w[6]&&d[7].0==w[7]};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_master_iterator(){let b:[u8;64]=kani::any();let mut seq:[u64;8]=kani::any();let old=seq;let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<8);let (lane,sequence)=seq.iter_mut().enumerate().nth(k).unwrap();let start=8*lane;*sequence=u64::from_le_bytes(b[start..start+8].try_into().unwrap());let law=lane==k&&seq[j]==if j==k{R::word64(&b,8*k)}else{old[j]};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_checkpoint_iterator(){let b:[u8;64]=kani::any();let mut seq:[u64;8]=kani::any();let old=seq;let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<8);let (lane,sequence)=seq.iter_mut().enumerate().nth(k).unwrap();let start=8*lane;*sequence=u64::from_le_bytes(b[start..start+8].try_into().unwrap());let reject=*sequence>POOL_V1_PAIR_CAPACITY;let law=lane==k&&reject==(R::word64(&b,8*k)>1048576)&&seq[j]==if j==k{R::word64(&b,8*k)}else{old[j]};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_frontier_iterator(){let raw:[[u32;8];20]=kani::any();let mut frontier=raw.map(|r|r.map(M31));let old=frontier;let k:usize=kani::any();let j:usize=kani::any();let c:usize=kani::any();let value:[u32;8]=kani::any();let next:u64=kani::any();kani::assume(k<20&&j<20&&c<8&&next<=1048576);let (level,node)=frontier.iter_mut().enumerate().nth(k).unwrap();*node=value.map(M31);let reject=(next>>level)&1==0&&*node!=v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level];let law=level==k&&reject==((next>>k)&1==0&&!R::eq_digest(&value,&R::EMPTY[k]))&&frontier[j][c].0==if j==k{value[c]}else{old[j][c].0};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_sequence_any_iterator(){let seq:[u64;8]=kani::any();let k:usize=kani::any();kani::assume(k<8);let mut it=seq[k..].iter();let value=it.next().unwrap();let law=(*value>POOL_V1_PAIR_CAPACITY)==(seq[k]>1048576)&&it.as_slice()==&seq[k+1..];assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_reserved_any_iterator(){let b:[u8;16]=kani::any();let k:usize=kani::any();kani::assume(k<16);let mut it=b[k..].iter();let byte=it.next().unwrap();let law=(*byte!=0)==(b[k]!=0)&&it.as_slice()==&b[k+1..];assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_master_box(){let a=NDB_any_master();let mut frame:[u8;16]=kani::any();let old=frame;let input:&PoolV1PairForestMasterV1=&a;let b=Box::new(*input);let j:usize=kani::any();kani::assume(j<16);let law=*b==a&&frame[j]==old[j];assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_master_map_error(){let err:bool=kani::any();let a=NDB_any_master();let r:Result<PoolV1PairForestMasterV1,u8>=if err{Err(kani::any())}else{Ok(a)};let actual:Result<Box<PoolV1PairForestMasterV1>,ProgramError>=(||{Ok(Box::new(r.map_err(|_|ProgramError::InvalidAccountData)?))})();let law=match actual{Err(e)=>err&&e==ProgramError::InvalidAccountData,Ok(b)=>!err&&*b==a};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_checkpoint_box(){let a=NDB_any_checkpoint();let mut frame:[u8;16]=kani::any();let old=frame;let input:&PoolV1PairForestCheckpointV1=&a;let b=Box::new(*input);let j:usize=kani::any();kani::assume(j<16);let law=*b==a&&frame[j]==old[j];assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_checkpoint_map_error(){let err:bool=kani::any();let a=NDB_any_checkpoint();let r:Result<PoolV1PairForestCheckpointV1,u8>=if err{Err(kani::any())}else{Ok(a)};let actual:Result<Box<PoolV1PairForestCheckpointV1>,ProgramError>=(||{Ok(Box::new(r.map_err(|_|ProgramError::InvalidAccountData)?))})();let law=match actual{Err(e)=>err&&e==ProgramError::InvalidAccountData,Ok(b)=>!err&&*b==a};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_lane_box(){let a=NDB_any_lane();let mut frame:[u8;16]=kani::any();let old=frame;let input:&PoolV1PairForestLaneStateV1=&a;let b=Box::new(*input);let j:usize=kani::any();kani::assume(j<16);let law=*b==a&&frame[j]==old[j];assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_lane_map_error(){let err:bool=kani::any();let a=NDB_any_lane();let r:Result<PoolV1PairForestLaneStateV1,u8>=if err{Err(kani::any())}else{Ok(a)};let actual:Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>=(||{Ok(Box::new(r.map_err(|_|ProgramError::InvalidAccountData)?))})();let law=match actual{Err(e)=>err&&e==ProgramError::InvalidAccountData,Ok(b)=>!err&&*b==a};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_bool_rejection(){let v:u8=kani::any();let actual:Result<bool,()>=match v{0=>Ok(false),1=>Ok(true),_=>Err(())};let law=match actual{Ok(x)=>v<2&&x==(v==1),Err(())=>v>1};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_master_chronology(){let has:bool=kani::any();let next:u64=kani::any();let s:[u64;8]=kani::any();let actual=(!has&&(next!=0||s!=[0u64;8]))||(has&&next==0);let law=actual==if has{next==0}else{next!=0||!R::zero_sequences(&s)};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_digest_limb(){let b:[u8;4]=kani::any();let value=u32::from_le_bytes(b);let a=M31::from_le_bytes(b);let law=match a{None=>value>=2147483647,Some(x)=>value<2147483647&&x.0==R::word32(&b,0)};assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_lane_empty_root(){let raw:[u32;8]=kani::any();let root=raw.map(M31);let next:u64=kani::any();let actual=next==0&&root!=v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH];let law=actual==(next==0&&!R::eq_digest(&raw,&R::EMPTY[20]));assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_lane_tree_header(){let b:[u8;8]=kani::any();let actual=b[..4]!=POOL_V1_TREE_STATE_MAGIC||b[4]!=POOL_V1_TREE_STATE_VERSION||b[5]!=POOL_V1_PAIR_TREE_DEPTH as u8||b[6]!=POOL_V1_TREE_HASH_VERSION||b[7]!=POOL_V1_DIGEST_ENCODING_VERSION;let law=actual==(!R::equal(&b[..4],b"ASPT")||b[4]!=1||b[5]!=20||b[6]!=3||b[7]!=1);assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_lane_header(){let b:[u8;8]=kani::any();let actual=b[..4]!=POOL_V1_PAIR_FOREST_LANE_MAGIC||b[4]!=POOL_V1_PAIR_FOREST_LANE_VERSION||usize::from(b[5])>=POOL_V1_PAIR_FOREST_LANE_COUNT||b[6]!=POOL_V1_PAIR_FOREST_LANE_COUNT as u8||b[7]!=POOL_V1_PAIR_TREE_DEPTH as u8;let law=actual==(!R::equal(&b[..4],b"ASL8")||b[4]!=2||b[5]>=8||b[6]!=8||b[7]!=20);assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_binding_window(){let b:[u8;32]=kani::any();let actual=b!=POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING;let law=actual==!R::equal(&b,&R::BINDING);assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_checkpoint_header(){let b:[u8;7]=kani::any();let actual=b[..4]!=aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC||b[4]!=aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION||b[5]!=POOL_V1_PAIR_FOREST_LANE_COUNT as u8||b[6]!=POOL_V1_DIGEST_ENCODING_VERSION;let law=actual==(!R::equal(&b[..4],b"ASC8")||b[4]!=2||b[5]!=8||b[6]!=1);assert!(law!=NDB_INVERSE,"NDB semantic law");}

#[kani::proof]
#[kani::stub(<[u8]>::copy_from_slice,crate::NDB_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDB_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NDB_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NDB_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NDB_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NDB_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NDB_master_header(){let b:[u8;7]=kani::any();let actual=b[..4]!=aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_MASTER_MAGIC||b[4]!=aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_MASTER_VERSION||b[5]!=POOL_V1_PAIR_FOREST_LANE_COUNT as u8||b[6]!=POOL_V1_DIGEST_ENCODING_VERSION;let law=actual==(!R::equal(&b[..4],b"ASM8")||b[4]!=2||b[5]!=8||b[6]!=1);assert!(law!=NDB_INVERSE,"NDB semantic law");}

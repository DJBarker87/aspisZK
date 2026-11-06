"""Native local-record constructor/child-boundary cuts, never whole decoder loops."""
from NJQ_patch import write_patch
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use crate::pool_v1::format::{PoolIdentityV1 as I,VerifierPolicyV1 as P,PoolV1FormatError as E};
use crate::pool_v1::incremental_merkle::PoolV1TreeError as T;
type F=PoolV1PairForestAccountErrorV1;
fn identity()->I{I{pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:aspis_core::field::M31(kani::any()),deployment_domain:kani::any()}}
fn policy()->P{P{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()}}
fn fmt_error()->E{let t:u8=kani::any();kani::assume(t<8);match t{0=>E::WrongLength,1=>E::WrongMagic,2=>E::WrongVersion,3=>E::NonZeroReserved,4=>E::NonCanonicalAssetId,5=>E::UnsupportedFlags,6=>E::ZeroRequiredBinding,_=>E::InvalidAuthorityMode}}
fn id_reply()->Result<I,E>{if kani::any(){Ok(identity())}else{Err(fmt_error())}}
fn policy_reply()->Result<P,E>{if kani::any(){Ok(policy())}else{Err(fmt_error())}}
fn account_reply()->Result<(),F>{let t:u8=kani::any();kani::assume(t<34);match t{
'''
units=['WrongLength','WrongMagic','WrongVersion','WrongLaneCount','WrongDigestEncoding','WrongDepth','WrongFormatBinding','NonZeroReserved','ZeroRequiredBinding','InvalidBoolean','InvalidMasterState','InvalidLane','LaneMasterMismatch','LaneOrderMismatch','LaneSequenceDecreased','DuplicateCheckpoint','CheckpointSequenceOverflow','NonCanonicalDigest','Identity','Policy']
trees=['TreeFull','InsufficientCapacity','IndexOutOfRange','RootMismatch','NonCanonicalFrontier','WrongLength','WrongMagic','WrongVersion','WrongDepth','WrongTreeHash','WrongDigestEncoding','NonCanonicalDigest','NonZeroReserved']
s+='0=>Ok(()),'+','.join(f'{i+1}=>Err(F::{v})' for i,v in enumerate(units))+','+','.join(f'{21+i}=>Err(F::Tree(T::{v}))' for i,v in enumerate(trees[:-1]))+',_=>Err(F::Tree(T::NonZeroReserved))}}\n'
s+='''fn view_i(p:&I,f:usize,i:usize)->u64{match f{0=>p.pool[i] as u64,1=>p.asset_mint[i] as u64,2=>p.token_program[i] as u64,3=>p.asset_id.0 as u64,_=>p.deployment_domain[i] as u64}}
fn view_p(p:&P,f:usize,i:usize)->u64{match f{0=>p.flags as u64,1=>p.registry_program[i] as u64,2=>p.registry_authority[i] as u64,_=>p.policy_binding[i] as u64}}
#[derive(Default)]struct ChildLog{policy_called:bool,policy_byte:u8,loop_entered:bool}
fn children(b:&[u8;384],idr:Result<I,E>,pr:Result<P,E>,i:usize,log:&mut ChildLog)->Result<(I,P),F>{
 let id=idr.map_err(|_|F::Identity)?;
 let arg=&b[MASTER_POLICY_OFFSET..312];log.policy_called=true;log.policy_byte=arg[i];
 let policy=pr.map_err(|_|F::Policy)?;log.loop_entered=true;Ok((id,policy))
}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn child_boundaries(){let b:[u8;384]=kani::any();let idr=id_reply();let pr=policy_reply();let i:usize=kani::any();kani::assume(i<104);let j:usize=kani::any();kani::assume(j<32);let f:usize=kani::any();kani::assume(f<9);let mut log=ChildLog::default();let frame:usize=kani::any();kani::assume(frame<384);let before=b[frame];let out=children(&b,idr,pr,i,&mut log);assert!(b[frame]==before);
 match idr{Err(_)=>{assert!(matches!(out,Err(F::Identity)));assert!(!log.policy_called&&!log.loop_entered);},Ok(id)=>{assert!(log.policy_called);assert!(log.policy_byte==b[208+i]);match pr{Err(_)=>{assert!(matches!(out,Err(F::Policy)));assert!(!log.loop_entered);},Ok(policy)=>{assert!(log.loop_entered);let (a,q)=out.expect("both child results were Ok");let v=if f<5{view_i(&a,f,j)}else{view_p(&q,f-5,j)};let expected=if f<5{view_i(&id,f,j)}else{view_p(&policy,f-5,j)};assert!((v==expected)!=cfg!(NJQ_invert));}}}}
}
fn word(b:&[u8],a:usize)->u64{u64::from_le_bytes([b[a],b[a+1],b[a+2],b[a+3],b[a+4],b[a+5],b[a+6],b[a+7]])}
fn checkpoint_constructor(b:&[u8;192],root:[aspis_core::field::M31;8],lanes:[u64;8])->Result<PoolV1PairForestCheckpointV1,F>{
 Ok(PoolV1PairForestCheckpointV1{bump:b[7],master:b[8..40].try_into().unwrap(),deployment_domain:b[40..72].try_into().unwrap(),checkpoint_sequence:u64::from_le_bytes(b[72..80].try_into().unwrap()),global_root:root,lane_sequences:lanes})
}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_constructor_cut(){let b:[u8;192]=kani::any();let roots:[u32;8]=kani::any();let root=[aspis_core::field::M31(roots[0]),aspis_core::field::M31(roots[1]),aspis_core::field::M31(roots[2]),aspis_core::field::M31(roots[3]),aspis_core::field::M31(roots[4]),aspis_core::field::M31(roots[5]),aspis_core::field::M31(roots[6]),aspis_core::field::M31(roots[7])];let lanes:[u64;8]=kani::any();let i:usize=kani::any();kani::assume(i<32);let j:usize=kani::any();kani::assume(j<8);let f:usize=kani::any();kani::assume(f<6);let frame:usize=kani::any();kani::assume(frame<192);let before=b[frame];let out=checkpoint_constructor(&b,root,lanes).expect("constructor returns the full Ok Result");assert!(b[frame]==before);assert!(root[j].0==roots[j]);let actual=match f{0=>out.bump as u64,1=>out.master[i] as u64,2=>out.deployment_domain[i] as u64,3=>out.checkpoint_sequence,4=>out.global_root[j].0 as u64,_=>out.lane_sequences[j]};let expected=match f{0=>b[7] as u64,1=>b[8+i] as u64,2=>b[40+i] as u64,3=>word(&b,72),4=>roots[j] as u64,_=>lanes[j]};assert!((actual==expected)!=cfg!(NJQ_invert));}
fn view_master(m:&PoolV1PairForestMasterV1,f:usize,i:usize,k:usize)->u64{match f{0=>m.bump as u64,1=>m.initialized_lane_mask as u64,2=>m.has_checkpoint as u64,3=>m.next_checkpoint_sequence,4=>m.last_checkpoint_lane_sequences[k],5..=9=>view_i(&m.identity,f-5,i),_=>view_p(&m.verifier_policy,f-10,i)}}
fn master_constructor(b:&[u8;384],id:I,policy:P,has_checkpoint:bool,lanes:[u64;8],reply:Result<(),F>,f:usize,i:usize,k:usize,log:&mut Option<u64>)->Result<PoolV1PairForestMasterV1,F>{
 let master=PoolV1PairForestMasterV1{bump:b[7],identity:id,verifier_policy:policy,initialized_lane_mask:b[MASTER_INITIALIZED_MASK_OFFSET],has_checkpoint,next_checkpoint_sequence:u64::from_le_bytes(b[MASTER_NEXT_CHECKPOINT_OFFSET..MASTER_INITIALIZED_MASK_OFFSET].try_into().unwrap()),last_checkpoint_lane_sequences:lanes};
 *log=Some(view_master(&master,f,i,k));reply?;Ok(master)
}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn master_constructor_cut(){let b:[u8;384]=kani::any();let id=identity();let policy=policy();let has:bool=kani::any();let lanes:[u64;8]=kani::any();let reply=account_reply();let f:usize=kani::any();kani::assume(f<14);let i:usize=kani::any();kani::assume(i<32);let k:usize=kani::any();kani::assume(k<8);let frame:usize=kani::any();kani::assume(frame<384);let before=b[frame];let mut log=None;let out=master_constructor(&b,id,policy,has,lanes,reply,f,i,k,&mut log);assert!(b[frame]==before);let expected=match f{0=>b[7] as u64,1=>b[48] as u64,2=>has as u64,3=>word(&b,40),4=>lanes[k],5..=9=>view_i(&id,f-5,i),_=>view_p(&policy,f-10,i)};assert!((log==Some(expected))!=cfg!(NJQ_invert));match reply{Err(e)=>assert!(matches!(out,Err(f) if e==f)),Ok(())=>{let m=out.expect("child Ok");assert!(view_master(&m,f,i,k)==expected);}}
}
'''
write_patch('NJQ_constructors',s)
print('Source child-boundary and constructor cuts generated; full 34-way account Result oracle retained.')

from NJI_patch import read_patch,write_patch
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs'],text=True)
a=s.index('fn validate_master(');start=s.index('{',a);end=start+1;depth=1
while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
body=s[start:end]
old='validate_verifier_policy_v1(&master.verifier_policy)'
anyold='master\n        .last_checkpoint_lane_sequences\n        .iter()\n        .any(|sequence| *sequence > POOL_V1_PAIR_CAPACITY)'
new='{*log=Some(master.verifier_policy); policy_reply}'
assert body.count(old)==body.count(anyold)==1
anynew='{*seq_log=Some(master.last_checkpoint_lane_sequences); seq_any}'
stage=body.replace(old,new).replace(anyold,anynew)
text='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type PF=crate::pool_v1::PoolV1FormatError;
type F=PoolV1PairForestAccountErrorV1;
fn stage(master:&PoolV1PairForestMasterV1,policy_reply:Result<(),PF>,seq_any:bool,log:&mut Option<VerifierPolicyV1>,seq_log:&mut Option<[u64;8]>)->Result<(),F> '''+stage+'''
fn policy_reply()->Result<(),PF>{let t:u8=kani::any();kani::assume(t<9);match t{0=>Ok(()),1=>Err(PF::WrongLength),2=>Err(PF::WrongMagic),3=>Err(PF::WrongVersion),4=>Err(PF::NonZeroReserved),5=>Err(PF::NonCanonicalAssetId),6=>Err(PF::UnsupportedFlags),7=>Err(PF::ZeroRequiredBinding),_=>Err(PF::InvalidAuthorityMode)}}
fn master()->PoolV1PairForestMasterV1{PoolV1PairForestMasterV1{bump:kani::any(),identity:PoolIdentityV1{pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:aspis_core::field::M31(kani::any()),deployment_domain:kani::any()},verifier_policy:VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()},initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()}}
#[derive(Debug,PartialEq,Eq)] enum Observation{Byte(u8),Word(u64),FieldWord(u32),Bit(bool)}
fn observe(m:&PoolV1PairForestMasterV1,f:usize,i:usize)->Observation{match f{
0=>Observation::Byte(m.bump),1=>Observation::Byte(m.identity.pool[i]),2=>Observation::Byte(m.identity.asset_mint[i]),3=>Observation::Byte(m.identity.token_program[i]),4=>Observation::FieldWord(m.identity.asset_id.0),5=>Observation::Byte(m.identity.deployment_domain[i]),6=>Observation::Byte(m.verifier_policy.flags),7=>Observation::Byte(m.verifier_policy.registry_program[i]),8=>Observation::Byte(m.verifier_policy.registry_authority[i]),9=>Observation::Byte(m.verifier_policy.policy_binding[i]),10=>Observation::Byte(m.initialized_lane_mask),11=>Observation::Bit(m.has_checkpoint),12=>Observation::Word(m.next_checkpoint_sequence),_=>Observation::Word(m.last_checkpoint_lane_sequences[i%8])}}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cut(){let m=master();let frame_f:usize=kani::any();kani::assume(frame_f<14);let frame_i:usize=kani::any();kani::assume(frame_i<32);let original=observe(&m,frame_f,frame_i);let q=policy_reply();let any:bool=kani::any();let mut log=None;let mut seq_log=None;let out=stage(&m,q,any,&mut log,&mut seq_log);assert!(observe(&m,frame_f,frame_i)==original);let i:usize=kani::any();kani::assume(i<32);
 let zero=m.identity.pool==[0;32]||m.identity.asset_mint==[0;32]||m.identity.token_program==[0;32]||m.identity.deployment_domain==[0;32];
 if zero{assert!(log.is_none());assert!(seq_log.is_none());assert!(out==Err(F::ZeroRequiredBinding));}else{
  let p=log.expect("policy entered");assert!(p.flags==m.verifier_policy.flags);assert!(p.registry_program[i]==m.verifier_policy.registry_program[i]);assert!(p.registry_authority[i]==m.verifier_policy.registry_authority[i]);assert!(p.policy_binding[i]==m.verifier_policy.policy_binding[i]);
  if q.is_err(){assert!(seq_log.is_none());}else{let logged=seq_log.expect("any entered");let j:usize=kani::any();kani::assume(j<8);assert!((logged[j]==m.last_checkpoint_lane_sequences[j])!=cfg!(NJI_invert));}
  let invalid=(!m.has_checkpoint&&(m.next_checkpoint_sequence!=0||m.last_checkpoint_lane_sequences!=[0;8]))||(m.has_checkpoint&&m.next_checkpoint_sequence==0);
  let expected=if q.is_err(){Err(F::Policy)}else if any||invalid{Err(F::InvalidMasterState)}else{Ok(())};assert!(out==expected);
 }
}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn any_step(){let values:[u64;8]=kani::any();let k:usize=kani::any();kani::assume(k<=8);let j:usize=kani::any();kani::assume(j<8);let original_j=values[j];let original_k=if k<8{values[k]}else{0};let mut it=values[k..].iter();let before=it.len();let got=it.next();assert!(values[j]==original_j);
 assert!(POOL_V1_PAIR_CAPACITY==1048576);
 if k<8{let value=got.expect("entered iteration");assert!((*value==original_k)!=cfg!(NJI_invert));let greater=*value>POOL_V1_PAIR_CAPACITY;assert!(greater==(original_k>1048576));assert!(it.len()+1==before);}else{assert!(got.is_none());assert!(it.len()==before);}
}
'''
write_patch('NJI_master_cut',text)
(E/'NJI_MASTER_CUT_FIDELITY.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_file_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),stage_sha256=hashlib.sha256(text.encode()).hexdigest(),replacements=[dict(old=old,new=new),dict(old=anyold,new=anynew)],erasure_restores_exact_body=stage.replace(new,old).replace(anynew,anyold)==body,loop_domain='ONE iteration, arbitrary values[8], k<=8 including exhaustion; no whole-loop native unrolling'),indent=2))

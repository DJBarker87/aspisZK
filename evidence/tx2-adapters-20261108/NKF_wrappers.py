from NKF_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
M='PoolV1PairForestMasterV1';C='PoolV1PairForestCheckpointV1';F='aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1'
COMMON='''use super::*;
use aspis_statement::pool_v1::{PoolV1PairForestAccountErrorV1 as F,PoolIdentityV1,VerifierPolicyV1};
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_field()->M31{M31(kani::any())}
fn any_digest()->[M31;8]{[any_field(),any_field(),any_field(),any_field(),any_field(),any_field(),any_field(),any_field()]}
fn any_error()->F{
 let i:u8=kani::any();kani::assume(i<=20);
 match i{0=>F::WrongLength,1=>F::WrongMagic,2=>F::WrongVersion,3=>F::WrongLaneCount,4=>F::WrongDigestEncoding,5=>F::WrongDepth,6=>F::WrongFormatBinding,7=>F::NonZeroReserved,8=>F::ZeroRequiredBinding,9=>F::InvalidBoolean,10=>F::InvalidMasterState,11=>F::InvalidLane,12=>F::LaneMasterMismatch,13=>F::LaneOrderMismatch,14=>F::LaneSequenceDecreased,15=>F::DuplicateCheckpoint,16=>F::CheckpointSequenceOverflow,17=>F::NonCanonicalDigest,18=>F::Identity,19=>F::Policy,_=>{
 use aspis_statement::pool_v1::PoolV1TreeError as T;let j:u8=kani::any();kani::assume(j<13);
 F::Tree(match j{0=>T::TreeFull,1=>T::InsufficientCapacity,2=>T::IndexOutOfRange,3=>T::RootMismatch,4=>T::NonCanonicalFrontier,5=>T::WrongLength,6=>T::WrongMagic,7=>T::WrongVersion,8=>T::WrongDepth,9=>T::WrongTreeHash,10=>T::WrongDigestEncoding,11=>T::NonCanonicalDigest,_=>T::NonZeroReserved})}}
}
fn any_master()->PoolV1PairForestMasterV1{PoolV1PairForestMasterV1{
 bump:kani::any(),identity:PoolIdentityV1{pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:any_field(),deployment_domain:kani::any()},verifier_policy:VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()},initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()}}
fn any_checkpoint()->PoolV1PairForestCheckpointV1{PoolV1PairForestCheckpointV1{bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),checkpoint_sequence:kani::any(),global_root:any_digest(),lane_sequences:kani::any()}}
'''
def wrapper(kind, fixed=None):
 typ=M if kind=='master' else C
 body=subprocess.check_output(['git','show','4bb3b3f5:'+P],text=True)
 name='decode_'+kind+'_box';start=body.index('fn '+name+'(');end=body.index('\n}',start)+2
 frozen=body[start:end];rawchild='decode_pool_v1_pair_forest_'+kind+'_v1(bytes)'
 # A source-ordered segment whose sole entered child reply is a universally
 # quantified typed parameter. Source site/arguments are composed separately.
 segment=frozen.replace('fn '+name+'(bytes: &[u8])','fn step(raw: Result<'+typ+', F>)').replace(rawchild,'raw')
 fields={'master':['a.bump==b.bump','a.identity.pool[index]==b.identity.pool[index]','a.identity.asset_mint[index]==b.identity.asset_mint[index]','a.identity.token_program[index]==b.identity.token_program[index]','a.identity.asset_id.0==b.identity.asset_id.0','a.identity.deployment_domain[index]==b.identity.deployment_domain[index]','a.verifier_policy.flags==b.verifier_policy.flags','a.verifier_policy.registry_program[index]==b.verifier_policy.registry_program[index]','a.verifier_policy.registry_authority[index]==b.verifier_policy.registry_authority[index]','a.verifier_policy.policy_binding[index]==b.verifier_policy.policy_binding[index]','a.initialized_lane_mask==b.initialized_lane_mask','a.has_checkpoint==b.has_checkpoint','a.next_checkpoint_sequence==b.next_checkpoint_sequence','a.last_checkpoint_lane_sequences[index%8]==b.last_checkpoint_lane_sequences[index%8]'],'checkpoint':['a.bump==b.bump','a.master[index]==b.master[index]','a.deployment_domain[index]==b.deployment_domain[index]','a.checkpoint_sequence==b.checkpoint_sequence','a.global_root[index%8].0==b.global_root[index%8].0','a.lane_sequences[index%8]==b.lane_sequences[index%8]']}[kind]
 rel='fn coordinate(a:&'+typ+',b:&'+typ+',field:u8,index:usize)->bool{match field{'+','.join(str(i)+'=>'+q for i,q in enumerate(fields))+',_=>false}}\n'
 segment=segment.replace(' F>)',' F>,field:u8,index:usize)')
 ann="""#[kani::requires(field<FIELD_COUNT && index<32)]
#[kani::ensures(|out| {let good=match (raw,out){(Ok(v),Ok(b))=>coordinate(&v,&**b,field,index),(Err(_),Err(ProgramError::InvalidAccountData))=>true,_=>false};if cfg!(NKF_invert){!good}else{good}})]
#[kani::modifies()]
""".replace('FIELD_COUNT',str(len(fields)))
 text=COMMON+'\n'+rel+ann+segment+'\n'+'''#[kani::proof_for_contract(step)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn wrapper_result(){let field:u8=kani::any();let index:usize=kani::any();kani::assume(field<FIELD_COUNT && index<32);let raw=if kani::any(){Ok(any_'''+kind+'''())}else{Err(any_error())};let _=step(raw,field,index);}
'''
 text=text.replace('FIELD_COUNT',str(len(fields)))
 if fixed is not None:
  text=text.replace('field<'+str(len(fields))+' && index<32','field=='+str(fixed)+' && index<32').replace('let field:u8=kani::any();','let field:u8='+str(fixed)+';')
 (E/('NKF_'+kind+'_wrapper.patch')).write_text('--- /dev/null\n+++ b/NKF_'+kind+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/('NKF_'+kind+'_SOURCE.json')).write_text(json.dumps(dict(function=name,source=P,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_body=frozen,body_sha256=sha(frozen.encode()),segment=segment,substitution={rawchild:'raw: full arbitrary child Result at SAME bytes'},modifies=[],domain='every raw child Result, all success fields unrestricted, all21 account errors and13 Tree errors; immutable input bytes'),indent=1)+'\n')
 return text
if __name__=='__main__':
 import sys
 a,kind,mode,*rest=sys.argv[1:];text=wrapper(kind,int(rest[0]) if rest else None)
 submit(a,'r1_pool_adapter::NKF_'+kind+'::wrapper_result',P,'NKF_'+kind,text,mode)

from pathlib import Path
E=Path(__file__).resolve().parent
t='''use super::*;
use aspis_statement::pool_v1::{PoolIdentityV1,VerifierPolicyV1};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn owned()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:false,is_writable:false,executable:false,length:Ok(kani::any()),bytes:Err(ProgramError::InvalidAccountData)}}
fn no_data(_: &OwnedAccount)->Result<&[u8],ProgramError>{panic!("no data read after selected authentication guard")}
fn no_pda(_: &[&[u8]],_: &Pubkey)->Result<Pubkey,solana_program::pubkey::PubkeyError>{panic!("no PDA/hash after selected authentication guard")}
fn check<const V2:bool,const G:usize>(wrong:bool){
 let verifier=Pubkey::new_from_array(kani::any());let mut pool=Pubkey::new_from_array(pool_program_id());
 let master_account=owned();let mut registry=owned();let entry=owned();
 let mut master=PoolV1PairForestMasterV1{bump:kani::any(),identity:PoolIdentityV1{pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:M31(kani::any()),deployment_domain:kani::any()},verifier_policy:VerifierPolicyV1{flags:POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY|if V2{POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT}else{0},registry_program:registry_program_id(),registry_authority:[0;32],policy_binding:AUDIT_POLICY_BINDING},initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()};
 registry.owner=Pubkey::new_from_array(registry_program_id());
 match G{
 0=>{pool=Pubkey::new_from_array(kani::any());kani::assume(pool.to_bytes()!=pool_program_id());},
 1=>master.verifier_policy.flags&=!POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
 2=>{let v:[u8;32]=kani::any();kani::assume(v!=registry_program_id());master.verifier_policy.registry_program=v;},
 3=>{let v:[u8;32]=kani::any();kani::assume(v!=[0;32]);master.verifier_policy.registry_authority=v;},
 4=>{let v:[u8;32]=kani::any();kani::assume(v!=AUDIT_POLICY_BINDING);master.verifier_policy.policy_binding=v;},
 5=>master.verifier_policy.flags|=4,
 6=>{registry.owner=Pubkey::new_from_array(kani::any());kani::assume(registry.owner.to_bytes()!=registry_program_id());},
 7=>registry.is_signer=true,8=>registry.is_writable=true,9=>registry.executable=true,
 _=>unreachable!()
 }
 let master_account=core::mem::ManuallyDrop::new(master_account);let registry=core::mem::ManuallyDrop::new(registry);let entry=core::mem::ManuallyDrop::new(entry);
 let result=authenticate_invariant_release_registry(&verifier,&pool,&master_account,&master,&registry,&entry,kani::any());
 assert!((result==Err(ProgramError::InvalidAccountData))!=wrong,"ordered authentication prefix and no data/PDA suffix");
}
'''
for v2 in [False,True]:
 for g in range(10):
  for wrong in [False,True]:
   name=('v2' if v2 else 'v1')+'_'+str(g)+('_wrong' if wrong else '')
   t+='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(Pubkey::create_program_address,no_pda)]\nfn '+name+'(){check::<'+str(v2).lower()+','+str(g)+'>('+str(wrong).lower()+');}\n'
p='programs/r1-cost-probe/src/NIV_auth.rs';(E/'NIV_auth.patch').write_text('--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(t.splitlines()))+' @@\n'+''.join('+'+l for l in t.splitlines(True)))

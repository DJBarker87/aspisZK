#[path="Client64_accounts.rs"]
mod client64_accounts;
use anyhow::{anyhow,ensure,Result};
use serde_json::{Value,json};
use solana_program::pubkey::Pubkey;
use std::{str::FromStr,fs,path::Path,time::Instant};
use aspis_core::field::{M31,P};
use aspis_pool::*;
use aspis_statement::pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1;
use aspis_statement::{pool_v1::*,derive_owner_key,encode_digest_canonical,poseidon2::Digest};
const SYSTEM:&str="11111111111111111111111111111111";
const TOKEN:&str="TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA";
const LOADER:&str="BPFLoaderUpgradeab1e11111111111111111111111";
const PROFILE:[u8;32]=[0x57,0x94,0x73,0x13,0xd2,0x32,0x64,0x1a,0xd8,0x15,0x7d,0x66,0xbf,0xaf,0xfa,0xb1,0x1e,0x4c,0x3a,0x99,0x33,0x1d,0x18,0xf4,0x4b,0xfa,0xca,0xb6,0x89,0x97,0x37,0xd3];
const RELEASE:[u8;32]=[0xe2,0x94,0xaf,0xbc,0x14,0xef,0x6a,0xfe,0x76,0xb8,0x47,0xde,0xf4,0x44,0x52,0xf8,0x4c,0xc3,0x72,0x80,0x64,0x65,0x76,0x07,0xb5,0x44,0xa5,0x39,0xca,0x9b,0x32,0x3a];
fn pk(q:&Value,k:&str)->Pubkey{Pubkey::from_str(q[k].as_str().unwrap()).unwrap()}
fn meta(p:Pubkey,s:bool,w:bool)->Value{json!([p.to_string(),s,w])}
fn ro(p:Pubkey)->Value{meta(p,false,false)}
fn rw(p:Pubkey)->Value{meta(p,false,true)}
fn ix(p:Pubkey,a:Vec<Value>,d:impl AsRef<[u8]>)->Value{json!({"program":p.to_string(),"accounts":a,"data":super::hex(d.as_ref())})}
fn err(e:impl std::fmt::Debug)->anyhow::Error{anyhow!("{e:?}")}
fn digest(seed:u32)->Digest{core::array::from_fn(|i|M31((seed+17*i as u32+1)%P))}
// Choose fixture notes whose deposit lane is also their spend output lane.
// This exercises existing deposit-created pages without manufacturing PDA data.
fn note(n:u32)->(Digest,Digest,Digest){let mut found=0;for j in 0..10000{let k=digest(10+j);let salt=digest(100+j);let cm=pool_v1_note_commitment(&derive_owner_key(&k),1000,M31(77),&salt);let nf=pool_v1_nullifier(&k,&salt);if pool_v1_pair_forest_deposit_lane_v1(&cm).unwrap()==pool_v1_pair_forest_output_lane_v1(&nf).unwrap(){if found==n{return(k,salt,cm)}found+=1;}}panic!("fixture note search exhausted")}

fn bytes(q:&Value,k:&str)->Vec<u8>{super::unhex(q[k].as_str().unwrap())}
pub fn run(q:&Value)->Result<Value>{
 let pool=pk(q,"pool");let mint=pk(q,"mint");let payer=pk(q,"payer");let registry=pk(q,"registry");let verifier=pk(q,"verifier");
 let system=Pubkey::from_str(SYSTEM)?;let token=Pubkey::from_str(TOKEN)?;
 let master=pool_v1_pair_forest_master_address(&pool,&mint).0;
 let lanes:Vec<Pubkey>=(0..8).map(|i|pool_v1_pair_forest_lane_address(&pool,&master,i).unwrap().0).collect();
 let vault=pool_v1_vault_token_account_address(&pool,&master).0;
 let authority=pool_v1_vault_authority_address(&pool,&master).0;
 let reg=aspis_registry::pool_v1_verifier_registry_v2_address(&registry,&master).0;
 let entry=aspis_registry::pool_v1_verifier_entry_v2_address(&registry,&master,&PROFILE,&RELEASE).0;
 match q["action"].as_str().unwrap(){
 "setup"=>{
 let init=PoolInitializationV1{asset_mint:mint.to_bytes(),token_program:token.to_bytes(),asset_id:M31(77),deployment_domain:[5;32],verifier_policy:VerifierPolicyV1{flags:POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY|POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,registry_program:registry.to_bytes(),registry_authority:[0;32],policy_binding:[7;32]}};
 let mut a=vec![rw(master)];a.extend(lanes.iter().copied().map(rw));a.extend([ro(mint),rw(vault),ro(token),meta(payer,true,true),ro(system)]);
 let slot=q["activation_slot"].as_u64().unwrap();let loader=Pubkey::from_str(LOADER)?;
 let rd=Pubkey::find_program_address(&[registry.as_ref()],&loader).0;let vd=Pubkey::find_program_address(&[verifier.as_ref()],&loader).0;
 let rh:[u8;32]=bytes(q,"registry_hash").try_into().unwrap();let vh:[u8;32]=bytes(q,"verifier_hash").try_into().unwrap();
 let reginit=ix(registry,vec![rw(reg),meta(payer,true,false),meta(pk(q,"funding_payer"),true,true),ro(system),ro(registry),ro(rd)],aspis_registry::encode_initialize_registry_v2(master.to_bytes(),[7;32],20,rh));
 // Governance authority must differ from the fee payer: exact ABI requires unique accounts.
 let gov=pk(q,"governance");let fee=pk(q,"funding_payer");
 let reginit= {let mut v=reginit;v["accounts"][1]=meta(gov,true,false);v};
 let schedule=ix(registry,vec![rw(reg),rw(entry),meta(gov,true,false),meta(fee,true,true),ro(system),ro(verifier),ro(vd)],aspis_registry::encode_schedule_profile_v2(0,verifier.to_bytes(),PROFILE,RELEASE,POOL_V1_PAIR_FOREST_TERMINAL_VERSION,slot,vh));
 let activate=ix(registry,vec![rw(reg),rw(entry),meta(gov,true,false)],aspis_registry::encode_simple_mutation_v2(aspis_registry::RegistryMutationOpcodeV1::Activate,1).map_err(err)?);
 let freeze=ix(registry,vec![rw(reg),meta(gov,true,false)],aspis_registry::encode_simple_mutation_v2(aspis_registry::RegistryMutationOpcodeV1::Freeze,2).map_err(err)?);
 Ok(json!({"master":master.to_string(),"lanes":lanes.iter().map(ToString::to_string).collect::<Vec<_>>(),"vault":vault.to_string(),"vault_authority":authority.to_string(),"registry_account":reg.to_string(),"entry":entry.to_string(),"initialize":ix(pool,a,encode_pair_forest_initialize_instruction_v1(&init).map_err(err)?),"registry_initialize":reginit,"schedule":schedule,"activate":activate,"freeze":freeze}))
 },
 "deposit"=>{
 let n=q["note"].as_u64().unwrap() as u32;let(k,salt,cm)=note(n);let lane=pool_v1_pair_forest_deposit_lane_v1(&cm).map_err(err)?;
 let page=pool_v1_root_page_address(&pool,&lanes[lane as usize],0).0;
 let mut a=vec![ro(master),rw(lanes[lane as usize]),rw(page),ro(mint),rw(pk(q,"source")),meta(pk(q,"token_owner"),true,false),rw(vault),ro(token)];
 if q["genesis"].as_bool().unwrap(){a.extend([meta(payer,true,true),ro(system)])}
 let d=encode_pair_forest_deposit_instruction_v1(&DepositRequestV1{owner_key:derive_owner_key(&k),amount:1000,salt,encrypted_note_payload:&[]}).map_err(err)?;
 let nf=pool_v1_nullifier(&k,&salt);let out=pool_v1_pair_forest_output_lane_v1(&nf).map_err(err)?;
 Ok(json!({"instruction":ix(pool,a,d),"lane_id":lane,"lane":lanes[lane as usize].to_string(),"page":page.to_string(),"output_lane_id":out,"output_lane":lanes[out as usize].to_string(),"output_page":pool_v1_root_page_address(&pool,&lanes[out as usize],0).0.to_string()}))
 },
 "checkpoint"=>{let seq=q["sequence"].as_u64().unwrap();let cp=pool_v1_pair_forest_checkpoint_address(&pool,&master,seq).0;let mut a=vec![rw(master)];a.extend(lanes.iter().copied().map(ro));a.extend([rw(cp),meta(payer,true,true),ro(system)]);Ok(json!({"checkpoint":cp.to_string(),"instruction":ix(pool,a,encode_pair_forest_checkpoint_instruction_v1())}))},
 "validate_settlement"=>{
 let lane=decode_pool_v1_pair_forest_lane_state_v1(&bytes(q,"lane_bytes"),&POOL_V1_PAIR_EMPTY_ROOTS).map_err(err)?;
 let marker=decode_pool_v1_nullifier_marker(&bytes(q,"marker_bytes")).map_err(err)?;
 let after=decode_pool_v1_pair_verified_afterstate_v1(&bytes(q,"candidate_bytes")).map_err(err)?;
 let(k,salt,_)=note(q["note"].as_u64().unwrap() as u32);
 ensure!(lane.master==master.to_bytes()&&lane.tree.next_leaf_index==after.next_pair_index&&lane.tree.root==after.next_root&&lane.tree.frontier==after.next_frontier,"settled lane differs from proved afterstate");
 ensure!(marker.pool==master.to_bytes()&&marker.deployment_domain==[5;32]&&marker.nullifier==pool_v1_nullifier(&k,&salt),"consumed marker identity differs");
 Ok(json!({"marker_matches":true,"lane_matches":true,"next_pair_index":after.next_pair_index,"root":super::hex(&encode_digest_canonical(&after.next_root))}))
 },
 "prove"=>prove(q,pool,master,&lanes,reg,entry,vault,authority,token,system),
 _=>Err(anyhow!("unknown action"))
 }
}
#[cfg(not(feature="r1p-check"))]
fn prove(_: &Value,_:Pubkey,_:Pubkey,_:&[Pubkey],_:Pubkey,_:Pubkey,_:Pubkey,_:Pubkey,_:Pubkey,_:Pubkey)->Result<Value>{Err(anyhow!("build with --features r1p-check"))}
#[cfg(feature="r1p-check")]
#[allow(clippy::too_many_arguments)]
fn prove(q:&Value,pool:Pubkey,master:Pubkey,lanes:&[Pubkey],reg:Pubkey,entry:Pubkey,vault:Pubkey,authority:Pubkey,token:Pubkey,system:Pubkey)->Result<Value>{
 use aspis_r1_cost_probe::RealR1_client;
 let mut accounts=client64_accounts::Accounts::parse(q)?;
 use aspis_prover::{HOST_HASH,state_only_entropy::DurableStateOnlyMaskNonceStore};
 let started=Instant::now();let n=q["note"].as_u64().unwrap() as u32;let(k,salt,cm)=note(n);let nf=pool_v1_nullifier(&k,&salt);
 let input_lane=pool_v1_pair_forest_deposit_lane_v1(&cm).map_err(err)? as usize;
 let output_lane=pool_v1_pair_forest_output_lane_v1(&nf).map_err(err)?;
 let lane=decode_pool_v1_pair_forest_lane_state_v1(&bytes(q,"lane_bytes"),&POOL_V1_PAIR_EMPTY_ROOTS).map_err(err)?;
 ensure!(lane.master==master.to_bytes()&&lane.lane_id==output_lane,"wrong live output lane");
 let cp=decode_pool_v1_pair_forest_checkpoint_v1(&bytes(q,"checkpoint_bytes")).map_err(err)?;
 ensure!(cp.master==master.to_bytes(),"checkpoint master mismatch");
 let mut leafs:Vec<Vec<Digest>>=vec![vec![];8];let mut input_index=0;
 for j in 0..2{let(_,_,c)=note(j);let l=pool_v1_pair_forest_deposit_lane_v1(&c).map_err(err)? as usize;if j==n{input_index=leafs[l].len() as u64;}leafs[l].push(PoolV1PairLeafWitnessV1::single_output(c).map_err(err)?.leaf_digest().map_err(err)?);}
 let mut roots=Vec::new();let mut siblings=[POOL_V1_PAIR_EMPTY_ROOTS[0];20];
 for l in 0..8{let mut nodes=leafs[l].clone();let mut idx=input_index as usize;for level in 0..20{if l==input_lane{siblings[level]=nodes.get(idx^1).copied().unwrap_or(POOL_V1_PAIR_EMPTY_ROOTS[level]);idx>>=1;}if nodes.is_empty(){nodes.push(POOL_V1_PAIR_EMPTY_ROOTS[level+1]);}else{if nodes.len()%2==1{nodes.push(POOL_V1_PAIR_EMPTY_ROOTS[level]);}nodes=nodes.chunks(2).map(|s|pool_v1_tree_parent(&s[0],&s[1])).collect();}}roots.push(nodes[0]);}
 let mut supers=[roots[0];3];let mut directions=[false;3];let mut idx=input_lane;
 for level in 0..3{supers[level]=roots[idx^1];directions[level]=idx%2==1;idx>>=1;roots=roots.chunks(2).map(|s|pool_v1_tree_parent(&s[0],&s[1])).collect();}
 ensure!(roots[0]==cp.global_root,"deposits do not reconstruct finalized anchor");
 let input=PoolV1PairForestInputNoteWitnessV1{pair:PoolV1PairInputNoteWitnessV1{nullifier_key:k,salt,value:1000,pair_leaf:PoolV1PairLeafWitnessV1::single_output(cm).map_err(err)?,selected_second:false,membership:PoolV1MembershipWitnessV1{siblings,index:input_index as u32}},super_root_siblings:supers,super_root_directions:directions};
 let live=PoolV1PairLiveSnapshotV1{pool:master.to_bytes(),deployment_domain:[5;32],sequence:lane.tree.next_leaf_index,next_pair_index:lane.tree.next_leaf_index,current_root:lane.tree.root,frontier:lane.tree.frontier};
 let context=PoolV1PaymentRelationContextV1{runtime_binding:PoolV1PaymentRuntimeBindingV1{pool:master.to_bytes(),deployment_domain:[5;32],anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,asset_id:M31(77)},spent_nullifiers:&[]};
 let withdrawal=q["withdrawal"].as_bool().unwrap();
 let change=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&digest(500+n)),salt:digest(600+n),value:if withdrawal{750}else{400}};
 let recipient=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&digest(300)),salt:digest(400),value:600};
 let payment=if withdrawal{PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1{pool:master.to_bytes(),deployment_domain:[5;32],anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,nullifier:nf,asset_id:M31(77),amount:250,destination_token_account:pk(q,"destination").to_bytes(),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,M31(77),&change.salt)})}else{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(PoolV1PrivateTransferPublicV1{pool:master.to_bytes(),deployment_domain:[5;32],anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,nullifier:nf,asset_id:M31(77),recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,recipient.value,M31(77),&recipient.salt),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,M31(77),&change.salt)})};
 let compiled=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&p,&PoolV1PairForestPrivateTransferWitnessV1{input,recipient,change},context,live),PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&p,&PoolV1PairForestWithdrawalWitnessV1{input,change},context,live)}.map_err(err)?;
 let common=PoolV1PairForestTerminalCommonV1{master_account:master.to_bytes(),checkpoint_account:pk(q,"checkpoint").to_bytes(),selected_lane_account:lanes[output_lane as usize].to_bytes(),output_lane,checkpoint_sequence:cp.checkpoint_sequence,historical_global_anchor:cp.global_root,lane_transition:compiled.public_statement};
 let statement=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)=>PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public},PoolV1PairForestTerminalPaymentV1::Withdrawal(public)=>PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}};
 let dir=Path::new(q["proof_dir"].as_str().unwrap());
 {use std::os::unix::fs::DirBuilderExt;fs::DirBuilder::new().mode(0o700).create(dir)?;}
 // Retain note recovery data on the host, alongside the durable nonce store.
 // This is excluded from evidence export even though these are public fixtures.
 let recovery=json!({"input_nullifier_key":super::hex(&encode_digest_canonical(&k)),"input_salt":super::hex(&encode_digest_canonical(&salt)),"input_value":1000,"asset_id":77,"output_lane":output_lane,"output_pair_index":lane.tree.next_leaf_index,"change":{"nullifier_key":super::hex(&encode_digest_canonical(&digest(500+n))),"salt":super::hex(&encode_digest_canonical(&change.salt)),"value":change.value,"selected_second":!withdrawal},"recipient":if withdrawal{Value::Null}else{json!({"nullifier_key":super::hex(&encode_digest_canonical(&digest(300))),"salt":super::hex(&encode_digest_canonical(&recipient.salt)),"value":recipient.value,"selected_second":false})}});
 {use std::io::Write;use std::os::unix::fs::OpenOptionsExt;let mut file=fs::OpenOptions::new().create_new(true).write(true).mode(0o600).open(dir.join("note-recovery.json"))?;file.write_all(serde_json::to_string_pretty(&recovery)?.as_bytes())?;file.sync_all()?;}
 let public=encode_pool_v1_pair_forest_terminal_statement_v1(&statement).map_err(err)?;
 let mut store=DurableStateOnlyMaskNonceStore::open(dir.join("mask-nonce-ledger"))?;
 let result=RealR1_client::prove_for_proof_accounts(statement.semantic_public(),&compiled,HOST_HASH,&mut store,|k| accounts.nonce(k)).map_err(err)?;
 let (attempt_index,proof_account)=accounts.selected(result.attempts)?;
 let mut proof=encode_pool_v1_pair_verified_afterstate_v1(&compiled.public_statement.candidate_afterstate).map_err(err)?.to_vec();proof.extend_from_slice(&result.proof);
 fs::write(dir.join("proof.bin"),&proof)?;fs::write(dir.join("statement.bin"),public)?;
 let request=PoolV1PairForestTerminalRequestV1{verifier_profile:PROFILE,verifier_release:RELEASE,pool_program:pool.to_bytes(),public:payment};
 let hints=pool_v1_pair_forest_terminal_bump_hints_v1(&pool,&master,&lanes[output_lane as usize],lane.tree.next_leaf_index,withdrawal);
 let data=encode_pair_forest_terminal_instruction_data_v1(&encode_pool_v1_pair_forest_terminal_request_v1(&request).map_err(err)?,hints);
 let page=pool_v1_root_page_address(&pool,&lanes[output_lane as usize],0).0;
 let marker=pool_v1_pair_forest_nullifier_marker_address(&pool,&master,&encode_digest_canonical(&nf))?.0;
 let mut a=vec![ro(master),ro(pk(q,"checkpoint")),rw(lanes[output_lane as usize]),rw(page),rw(marker),meta(pk(q,"payer"),true,true),ro(system),ro(reg),ro(entry),ro(pk(q,"verifier"))];
 let stage1_accounts=accounts.publication(result.attempts,&mut a,pk(q,"public_account"),pk(q,"verifier_checkpoint"))?;
 if withdrawal{a.extend([ro(pk(q,"mint")),rw(vault),rw(pk(q,"destination")),ro(authority),ro(token)]);}
 a.push(ro(pk(q,"verifier_checkpoint")));
 Ok(json!({"client_route":"selected64-proof-account-v1","proof_account":proof_account.to_string(),"attempt_index":attempt_index,"prove_wall_seconds":started.elapsed().as_secs_f64(),"attempts":result.attempts,"p_r1":true,"mask_audit":format!("{:?}",result.audit),"proof_bytes":proof.len(),"proof_upload_count":proof.len().div_ceil(3763),"statement_upload_count":1,"marker":marker.to_string(),"output_lane":lanes[output_lane as usize].to_string(),"page":page.to_string(),"needs_zero_page":lane.tree.next_leaf_index==0,"settle":ix(pool,a,data),"stage1":ix(pk(q,"verifier"),stage1_accounts.as_array().unwrap().clone(),[3,10])}))
}

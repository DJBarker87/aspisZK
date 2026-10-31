#[path="accounts.rs"]
mod client64_accounts;
use super::diagnostics::{anyhow,ensure,Result,err};
use serde_json::Value;
use solana_program::pubkey::Pubkey;
use std::{str::FromStr,fs,path::Path,time::Instant};
use aspis_pool::*;
use aspis_statement::{pool_v1::*,derive_owner_key,encode_digest_canonical};
const SYSTEM:&str="11111111111111111111111111111111";
const TOKEN:&str="TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA";

const PROFILE:[u8;32]=[0x57,0x94,0x73,0x13,0xd2,0x32,0x64,0x1a,0xd8,0x15,0x7d,0x66,0xbf,0xaf,0xfa,0xb1,0x1e,0x4c,0x3a,0x99,0x33,0x1d,0x18,0xf4,0x4b,0xfa,0xca,0xb6,0x89,0x97,0x37,0xd3];
const RELEASE:[u8;32]=[0xe2,0x94,0xaf,0xbc,0x14,0xef,0x6a,0xfe,0x76,0xb8,0x47,0xde,0xf4,0x44,0x52,0xf8,0x4c,0xc3,0x72,0x80,0x64,0x65,0x76,0x07,0xb5,0x44,0xa5,0x39,0xca,0x9b,0x32,0x3a];
fn pk(q:&Value,k:&str)->Pubkey{Pubkey::from_str(&crate::public_text(q,k)).unwrap()}
fn meta(p:Pubkey,s:bool,w:bool)->Value{Value::Array(vec![Value::String(p.to_string()),Value::Bool(s),Value::Bool(w)])}
fn ro(p:Pubkey)->Value{meta(p,false,false)}
fn rw(p:Pubkey)->Value{meta(p,false,true)}
fn ix(p:Pubkey,a:Vec<Value>,d:impl AsRef<[u8]>)->Value{
 let mut o=serde_json::Map::new();o.insert("program".to_owned(),Value::String(p.to_string()));o.insert("accounts".to_owned(),Value::Array(a));o.insert("data".to_owned(),Value::String(super::hex(d.as_ref())));Value::Object(o)
}
fn number(n:usize)->Value{Value::Number(serde_json::Number::from(n as u64))}

fn bytes(q:&Value,k:&str)->Vec<u8>{super::unhex(&crate::public_text(q,k))}
pub fn run(q:&Value)->Result<Value>{
 ensure!(crate::public_field(q,"action").as_str()==Some("prove"),"user client supports prove only");
 let pool=pk(q,"pool");let mint=pk(q,"mint");let registry=pk(q,"registry");
 let master=pool_v1_pair_forest_master_address(&pool,&mint).0;
 let lanes:Vec<Pubkey>=(0..8).map(|i|pool_v1_pair_forest_lane_address(&pool,&master,i).unwrap().0).collect();
 let vault=pool_v1_vault_token_account_address(&pool,&master).0;
 let authority=pool_v1_vault_authority_address(&pool,&master).0;
 let reg=aspis_registry::pool_v1_verifier_registry_v2_address(&registry,&master).0;
 let entry=aspis_registry::pool_v1_verifier_entry_v2_address(&registry,&master,&PROFILE,&RELEASE).0;
 prove(q,pool,master,&lanes,reg,entry,vault,authority,Pubkey::from_str(TOKEN).map_err(err)?,Pubkey::from_str(SYSTEM).map_err(err)?)
}
#[cfg(not(feature="r1p-check"))]
fn prove(_: &Value,_:Pubkey,_:Pubkey,_:&[Pubkey],_:Pubkey,_:Pubkey,_:Pubkey,_:Pubkey,_:Pubkey,_:Pubkey)->Result<Value>{Err(anyhow!("build with --features r1p-check"))}
#[cfg(feature="r1p-check")]
#[allow(clippy::too_many_arguments)]
fn prove(q:&Value,pool:Pubkey,master:Pubkey,lanes:&[Pubkey],reg:Pubkey,entry:Pubkey,vault:Pubkey,authority:Pubkey,token:Pubkey,system:Pubkey)->Result<Value>{
 use aspis_r1_cost_probe::RealR1_client;
 let accounts=client64_accounts::Accounts::parse(q)?;
 use aspis_prover::{HOST_HASH,state_only_entropy::DurableStateOnlyMaskNonceStore};
 let started=Instant::now();let secrets=super::wallet::read(q)?;
 let k=secrets.input_key;let salt=secrets.input_salt;let asset=secrets.asset;
 let input_value=u32::try_from(secrets.input_value).map_err(err)?;
 let recipient_value=u32::try_from(secrets.recipient_value).map_err(err)?;
 let cm=pool_v1_note_commitment(&derive_owner_key(&k),input_value,asset,&salt);
 let nf=pool_v1_nullifier(&k,&salt);
 let output_lane=pool_v1_pair_forest_output_lane_v1(&nf).map_err(err)?;
 let lane=decode_pool_v1_pair_forest_lane_state_v1(&bytes(q,"lane_bytes"),&POOL_V1_PAIR_EMPTY_ROOTS).map_err(err)?;
 ensure!(lane.master==master.to_bytes()&&lane.lane_id==output_lane,"wrong live output lane");
 let cp=decode_pool_v1_pair_forest_checkpoint_v1(&bytes(q,"checkpoint_bytes")).map_err(err)?;
 ensure!(cp.master==master.to_bytes(),"checkpoint master mismatch");
 let input=super::membership::input(q,cm,k,salt,input_value,cp.global_root)?;
 let live=PoolV1PairLiveSnapshotV1{pool:master.to_bytes(),deployment_domain:cp.deployment_domain,sequence:lane.tree.next_leaf_index,next_pair_index:lane.tree.next_leaf_index,current_root:lane.tree.root,frontier:lane.tree.frontier};
 let context=PoolV1PaymentRelationContextV1{runtime_binding:PoolV1PaymentRuntimeBindingV1{pool:master.to_bytes(),deployment_domain:cp.deployment_domain,anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,asset_id:asset},spent_nullifiers:&[]};
 let withdrawal=crate::public_field(q,"withdrawal").as_bool().unwrap();
 let output_value=if withdrawal{u32::try_from(crate::public_field(q,"withdrawal_amount").as_u64().ok_or_else(||anyhow!("missing withdrawal amount"))?).map_err(err)?}else{recipient_value};
 let change_value=input_value.checked_sub(output_value).ok_or_else(||anyhow!("insufficient input value"))?;
 let change=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&secrets.change_key),salt:secrets.change_salt,value:change_value};
 let recipient=PoolV1OutputNoteWitnessV1{owner_key:secrets.recipient_owner,salt:secrets.recipient_salt,value:recipient_value};
 let payment=if withdrawal{PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1{pool:master.to_bytes(),deployment_domain:cp.deployment_domain,anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,nullifier:nf,asset_id:asset,amount:output_value,destination_token_account:pk(q,"destination").to_bytes(),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,asset,&change.salt)})}else{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(PoolV1PrivateTransferPublicV1{pool:master.to_bytes(),deployment_domain:cp.deployment_domain,anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,nullifier:nf,asset_id:asset,recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,recipient.value,asset,&recipient.salt),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,asset,&change.salt)})};
 let compiled=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&p,&PoolV1PairForestPrivateTransferWitnessV1{input,recipient,change},context,live),PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&p,&PoolV1PairForestWithdrawalWitnessV1{input,change},context,live)}.map_err(err)?;
 let common=PoolV1PairForestTerminalCommonV1{master_account:master.to_bytes(),checkpoint_account:pk(q,"checkpoint").to_bytes(),selected_lane_account:lanes[output_lane as usize].to_bytes(),output_lane,checkpoint_sequence:cp.checkpoint_sequence,historical_global_anchor:cp.global_root,lane_transition:compiled.public_statement};
 let statement=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)=>PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public},PoolV1PairForestTerminalPaymentV1::Withdrawal(public)=>PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}};
 let public_dir=crate::public_text(q,"proof_dir");let dir=Path::new(&public_dir);
 super::create_private_directory(dir)?;
 // Retain the exact wallet record for recovery with restrictive permissions.
 super::wallet::retain(dir,&secrets.record)?;
 let public=encode_pool_v1_pair_forest_terminal_statement_v1(&statement).map_err(err)?;
 let mut store=DurableStateOnlyMaskNonceStore::open(dir.join("mask-nonce-ledger")).map_err(err)?;
 let result=RealR1_client::prove_for_proof_accounts(statement.semantic_public(),&compiled,HOST_HASH,&mut store,|k| accounts.nonce(k)).map_err(err)?;
 let (attempt_index,proof_account)=accounts.selected(result.attempts)?;
 let mut proof=encode_pool_v1_pair_verified_afterstate_v1(&compiled.public_statement.candidate_afterstate).map_err(err)?.to_vec();proof.extend_from_slice(&result.proof);
 fs::write(dir.join("proof.bin"),&proof).map_err(err)?;fs::write(dir.join("statement.bin"),public).map_err(err)?;
 let request=PoolV1PairForestTerminalRequestV1{verifier_profile:PROFILE,verifier_release:RELEASE,pool_program:pool.to_bytes(),public:payment};
 let hints=pool_v1_pair_forest_terminal_bump_hints_v1(&pool,&master,&lanes[output_lane as usize],lane.tree.next_leaf_index,withdrawal);
 let data=encode_pair_forest_terminal_instruction_data_v1(&encode_pool_v1_pair_forest_terminal_request_v1(&request).map_err(err)?,hints);
 let page=pool_v1_root_page_address(&pool,&lanes[output_lane as usize],0).0;
 let marker=pool_v1_pair_forest_nullifier_marker_address(&pool,&master,&encode_digest_canonical(&nf)).map_err(err)?.0;
 let mut a=vec![ro(master),ro(pk(q,"checkpoint")),rw(lanes[output_lane as usize]),rw(page),rw(marker),meta(pk(q,"payer"),true,true),ro(system),ro(reg),ro(entry),ro(pk(q,"verifier"))];
 let stage1_accounts=accounts.publication(result.attempts,&mut a,pk(q,"public_account"),pk(q,"verifier_checkpoint"))?;
 if withdrawal{a.extend([ro(pk(q,"mint")),rw(vault),rw(pk(q,"destination")),ro(authority),ro(token)]);}
 a.push(ro(pk(q,"verifier_checkpoint")));
 let mut out=serde_json::Map::new();
 out.insert("client_route".to_owned(),Value::String("selected64-proof-account-v1".to_owned()));
 out.insert("proof_account".to_owned(),Value::String(proof_account.to_string()));
 out.insert("attempt_index".to_owned(),number(attempt_index));
 out.insert("prove_wall_seconds".to_owned(),Value::Number(serde_json::Number::from_f64(started.elapsed().as_secs_f64()).unwrap()));
 out.insert("attempts".to_owned(),number(result.attempts));
 out.insert("p_r1".to_owned(),Value::Bool(true));
 out.insert("proof_bytes".to_owned(),number(proof.len()));
 out.insert("proof_upload_count".to_owned(),number(proof.len().div_ceil(3763)));
 out.insert("statement_upload_count".to_owned(),number(1));
 out.insert("marker".to_owned(),Value::String(marker.to_string()));
 out.insert("output_lane".to_owned(),Value::String(lanes[output_lane as usize].to_string()));
 out.insert("page".to_owned(),Value::String(page.to_string()));
 out.insert("needs_zero_page".to_owned(),Value::Bool(lane.tree.next_leaf_index==0));
 out.insert("settle".to_owned(),ix(pool,a,data));
 out.insert("stage1".to_owned(),ix(pk(q,"verifier"),match stage1_accounts { Value::Array(a)=>a,_=>return Err(anyhow!("publication shape")) },[3,10]));
 Ok(Value::Object(out))
}

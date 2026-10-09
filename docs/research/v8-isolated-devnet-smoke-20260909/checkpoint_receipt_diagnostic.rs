//! LOCAL diagnostic only: finalized account snapshots are injected as inputs.
//! Receipt preparation and checkpoint persistence execute actual Pool SBF.
use std::{fs,str::FromStr};
use base64::{Engine,engine::general_purpose::STANDARD};
use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_instruction::{Instruction,AccountMeta};
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_message::{v1::{Message,TransactionConfig},VersionedMessage};
use solana_transaction::versioned::VersionedTransaction;
use serde_json::{Value,json};
use aspis_statement::pool_v1::*;
fn tx(svm:&LiteSVM,payer:&Keypair,ix:Instruction)->anyhow::Result<VersionedTransaction>{
 let config=TransactionConfig::empty().with_priority_fee(10000).with_compute_unit_limit(1_200_000).with_loaded_accounts_data_size_limit(8*1024*1024).with_heap_size(256*1024);
 let msg=Message::try_compile_with_config(&payer.pubkey(),&[ix],svm.latest_blockhash(),config)?;
 Ok(VersionedTransaction::try_new(VersionedMessage::V1(msg),&[payer])?)
}
fn main()->anyhow::Result<()> {
 let args:Vec<String>=std::env::args().collect();
 let snapshot:Value=serde_json::from_slice(&fs::read(&args[1])?)?;
 let plan:Value=serde_json::from_slice(&fs::read(&args[2])?)?;
 let ins=&plan["checkpoint_instruction"];
 let program=Address::from_str(ins["program"].as_str().unwrap())?;
 let master=Address::from_str(plan["master"].as_str().unwrap())?;
 let checkpoint=Address::from_str(plan["checkpoint"].as_str().unwrap())?;
 let payer=Keypair::new_from_array([91;32]);
 let mut svm=LiteSVM::new();svm.add_program(program,&fs::read(&args[3])?)?;
 for(k,v)in snapshot["accounts"].as_object().unwrap(){
  if v.is_null() || v["executable"]==true {continue;}
  let address=Address::from_str(k)?;if address==program{continue;}
  svm.set_account(address,Account{lamports:v["lamports"].as_u64().unwrap(),data:STANDARD.decode(v["data"][0].as_str().unwrap())?,owner:Address::from_str(v["owner"].as_str().unwrap())?,executable:false,rent_epoch:v["rentEpoch"].as_u64().unwrap()})?;
 }
 svm.airdrop(&payer.pubkey(),10_000_000_000).unwrap();
 let lanes:Vec<Address>=plan["lanes"].as_array().unwrap().iter().map(|k|Address::from_str(k.as_str().unwrap()).unwrap()).collect();
 let receipts:Vec<Address>=lanes.iter().map(|k|Address::find_program_address(&[b"aspis-v8-lane-validation",k.as_ref()],&program).0).collect();
 let states:Vec<_>=lanes.iter().map(|k|decode_pool_v1_pair_forest_lane_state_v1(&svm.get_account(k).unwrap().data,&aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS).unwrap()).collect();
 let states:[PoolV1PairForestLaneStateV1;8]=states.try_into().unwrap();
 assert!(states.iter().all(|s|s.tree.next_leaf_index>0));
 let original_master=svm.get_account(&master).unwrap();
 let m=decode_pool_v1_pair_forest_master_v1(&original_master.data).unwrap();
 let global=aspis_pool::pool_v1_pair_forest_global_root_v1(&states.each_ref().map(|s|s.tree.root));
 let expected=plan_pool_v1_pair_forest_checkpoint_v1(&m,&states,global).unwrap();
 for i in 0..8 {
  let ix=Instruction{program_id:program,accounts:vec![AccountMeta::new_readonly(master,false),AccountMeta::new_readonly(lanes[i],false),AccountMeta::new(receipts[i],false),AccountMeta::new(payer.pubkey(),true),AccountMeta::new_readonly(Address::default(),false)],data:vec![b'A',b'S',b'8',b'V',1,i as u8,0,0]};
  if i==0 {
   for(offset,name)in [(96,"bad-root-preparation"),(128,"bad-frontier-preparation")] {
    let good=svm.get_account(&lanes[i]).unwrap();let mut bad=good.clone();bad.data[offset]^=1;svm.set_account(lanes[i],bad)?;
    let result=svm.simulate_transaction(tx(&svm,&payer,ix.clone())?);assert!(result.is_err());
    let e=result.err().unwrap();println!("{}",json!({"control":name,"rejected":true,"cu":e.meta.compute_units_consumed,"error":format!("{:?}",e.err)}));
    assert!(svm.get_account(&receipts[i]).is_none());assert_eq!(svm.get_account(&master).unwrap(),original_master);
    svm.set_account(lanes[i],good)?;
   }
  }
  let result=svm.send_transaction(tx(&svm,&payer,ix)?).map_err(|e|anyhow::anyhow!("prepare {}: {:?}",i,e))?;
  println!("{}",json!({"phase":"prepare","lane":i,"cu":result.compute_units_consumed}));
 }
 let mut accounts:Vec<AccountMeta>=ins["accounts"].as_array().unwrap().iter().map(|v|{let signer=v["signer"].as_bool().unwrap();let key=if signer{payer.pubkey()}else{Address::from_str(v["key"].as_str().unwrap()).unwrap()};if v["writable"].as_bool().unwrap(){AccountMeta::new(key,signer)}else{AccountMeta::new_readonly(key,signer)}}).collect();
 accounts.extend(receipts.iter().map(|k|AccountMeta::new_readonly(*k,false)));
 let ix=Instruction{program_id:program,accounts,data:b"AS8K\x01\x08\x01\x00".to_vec()};
 for control in ["stale-lane","wrong-receipt-owner","corrupt-receipt","swapped-receipts"] {
  let mut bad_ix=ix.clone();let good_lane=svm.get_account(&lanes[0]).unwrap();let good_receipt=svm.get_account(&receipts[0]).unwrap();
  match control {
   "stale-lane"=>{let mut a=good_lane.clone();a.data[96]^=1;svm.set_account(lanes[0],a)?;},
   "wrong-receipt-owner"=>{let mut a=good_receipt.clone();a.owner=Address::default();svm.set_account(receipts[0],a)?;},
   "corrupt-receipt"=>{let mut a=good_receipt.clone();a.data[40+96]^=1;svm.set_account(receipts[0],a)?;},
   _=>bad_ix.accounts.swap(12,13)
  }
  let result=svm.simulate_transaction(tx(&svm,&payer,bad_ix)?);assert!(result.is_err());let e=result.err().unwrap();
  println!("{}",json!({"control":control,"rejected":true,"cu":e.meta.compute_units_consumed,"error":format!("{:?}",e.err),"master_checkpoint_unchanged":true}));
  assert_eq!(svm.get_account(&master).unwrap(),original_master);assert!(svm.get_account(&checkpoint).is_none());
  svm.set_account(lanes[0],good_lane)?;svm.set_account(receipts[0],good_receipt)?;
 }
 let exact=tx(&svm,&payer,ix)?;let simulation=svm.simulate_transaction(exact.clone()).map_err(|e|anyhow::anyhow!("final simulation {:?}",e))?;
 let result=svm.send_transaction(exact).map_err(|e|anyhow::anyhow!("final send {:?}",e))?;
 assert_eq!(svm.get_account(&checkpoint).unwrap().data,encode_pool_v1_pair_forest_checkpoint_v1(&expected.checkpoint).unwrap());
 assert_eq!(svm.get_account(&master).unwrap().data,encode_pool_v1_pair_forest_master_v1(&expected.next_master).unwrap());
 for k in &lanes {assert_eq!(svm.get_account(k).unwrap().data,STANDARD.decode(snapshot["accounts"][k.to_string()]["data"][0].as_str().unwrap())?);}
 println!("{}",json!({"phase":"checkpoint","all_eight_lanes_populated":true,"cu":result.compute_units_consumed,"simulation_cu":simulation.meta.compute_units_consumed,"declared_cu":1200000,"exact_canonical_checkpoint_and_master":true,"lanes_unchanged":true,"evidence_kind":"local diagnostic only"}));
 Ok(())
}

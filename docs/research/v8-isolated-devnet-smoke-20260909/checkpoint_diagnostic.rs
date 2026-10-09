//! Diagnostic replay of the preserved finalized eight-lane snapshot.
//! Account injection is ONLY for local regression, never live settlement evidence.
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
fn main()->anyhow::Result<()> {
 let args:Vec<String>=std::env::args().collect();
 let snapshot:Value=serde_json::from_slice(&fs::read(&args[1])?)?;
 let plan:Value=serde_json::from_slice(&fs::read(&args[2])?)?;
 let ins=&plan["checkpoint_instruction"];
 let program=Address::from_str(ins["program"].as_str().unwrap())?;
 let payer=Keypair::new_from_array([91;32]);
 for control in ["valid","root-corruption","frontier-corruption"] {
 let mut svm=LiteSVM::new();
 svm.add_program(program,&fs::read(&args[3])?)?;
 for (k,v) in snapshot["accounts"].as_object().unwrap() {
  if v.is_null() {continue;}
  let address=Address::from_str(k)?;
  if address==program || v["executable"]==true {continue;}
  let mut data=STANDARD.decode(v["data"][0].as_str().unwrap())?;
  if k==plan["lanes"][0].as_str().unwrap() {
   // Root at lane header 80 + tree header 16; frontier follows root.
   if control=="root-corruption" {data[96]^=1;}
   if control=="frontier-corruption" {data[128]^=1;}
  }
  svm.set_account(address,Account{lamports:v["lamports"].as_u64().unwrap(),data,owner:Address::from_str(v["owner"].as_str().unwrap())?,executable:false,rent_epoch:v["rentEpoch"].as_u64().unwrap()})?;
 }
 svm.airdrop(&payer.pubkey(),10_000_000_000).unwrap();
 let accounts=ins["accounts"].as_array().unwrap().iter().map(|v| {
  let signer=v["signer"].as_bool().unwrap();
  let key=if signer {payer.pubkey()} else {Address::from_str(v["key"].as_str().unwrap()).unwrap()};
  if v["writable"].as_bool().unwrap(){AccountMeta::new(key,signer)}else{AccountMeta::new_readonly(key,signer)}
 }).collect();
 let ix=Instruction{program_id:program,accounts,data:STANDARD.decode(ins["data"].as_str().unwrap())?};
 let config=TransactionConfig::empty().with_priority_fee(10000).with_compute_unit_limit(1_200_000).with_loaded_accounts_data_size_limit(8*1024*1024).with_heap_size(256*1024);
 let msg=Message::try_compile_with_config(&payer.pubkey(),&[ix],svm.latest_blockhash(),config)?;
 let tx=VersionedTransaction::try_new(VersionedMessage::V1(msg),&[&payer])?;
 let result=svm.simulate_transaction(tx);
 match result {Ok(v)=>println!("{}",json!({"control":control,"ok":true,"cu":v.meta.compute_units_consumed,"logs":v.meta.logs})), Err(v)=>println!("{}",json!({"control":control,"ok":false,"cu":v.meta.compute_units_consumed,"error":format!("{:?}",v.err),"logs":v.meta.logs}))};
 }
 Ok(())
}

//! Host-only TxV1 signer for the config-driven devnet driver. Keys never leave host.
#[path="devnet_spend/diagnostics.rs"]
mod diagnostics;
use diagnostics::{Result,ensure,anyhow,err};
#[cfg(all(not(test), not(all(target_os = "linux", panic = "abort", getrandom_backend = "linux_raw"))))]
compile_error!("build the Linux client with build-client.sh");
use serde_json::Value;
use solana_address::Address;
use solana_instruction::{Instruction,AccountMeta};
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_message::{v1::{Message,TransactionConfig},VersionedMessage};
use solana_transaction::versioned::VersionedTransaction;
use std::{io::{self,Read},str::FromStr,fs};
#[path="devnet_spend/plan.rs"]
mod plan;
fn main() -> std::process::ExitCode {
 diagnostics::initialize();
 match run() {
  Ok(()) => std::process::ExitCode::SUCCESS,
  Err(e) => { diagnostics::report(e); std::process::ExitCode::FAILURE }
 }
}
fn run()->Result<()> {
 let mut s=String::new();io::stdin().read_to_string(&mut s).map_err(err)?;let q:Value=serde_json::from_str(&s).map_err(err)?;
 if q.get("action").is_some(){println!("{}",plan::run(&q)?);return Ok(())}
 let keys:Vec<Keypair>=q["keys"].as_array().unwrap().iter().map(|p|{let b:Vec<u8>=serde_json::from_slice(&fs::read(p.as_str().unwrap()).unwrap()).unwrap();Keypair::try_from(b.as_slice()).unwrap()}).collect();
 let ixs:Vec<Instruction>=q["instructions"].as_array().unwrap().iter().map(|i|Instruction{program_id:Address::from_str(i["program"].as_str().unwrap()).unwrap(),accounts:i["accounts"].as_array().unwrap().iter().map(|a|AccountMeta{pubkey:Address::from_str(a[0].as_str().unwrap()).unwrap(),is_signer:a[1].as_bool().unwrap(),is_writable:a[2].as_bool().unwrap()}).collect(),data:unhex(i["data"].as_str().unwrap())}).collect();
 let conf=TransactionConfig::empty().with_priority_fee(10000).with_compute_unit_limit(1_400_000).with_loaded_accounts_data_size_limit(8*1024*1024).with_heap_size(256*1024);
 let m=Message::try_compile_with_config(&keys[0].pubkey(),&ixs,q["blockhash"].as_str().unwrap().parse().map_err(err)?,conf).map_err(err)?;
 let refs:Vec<&Keypair>=keys.iter().collect();let tx=VersionedTransaction::try_new(VersionedMessage::V1(m),&refs).map_err(err)?;
 let b=wincode::serialize(&tx).map_err(err)?;ensure!(b.len()<=4096,"TxV1 exceeds 4096 bytes");
 println!("{}",serde_json::json!({"hex":hex(&b),"signature":tx.signatures[0].to_string(),"bytes":b.len()}));Ok(())
}
fn unhex(s:&str)->Vec<u8>{(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(b:&[u8])->String{b.iter().map(|b|format!("{b:02x}")).collect()}

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
use std::{io::{self,Read},str::FromStr};
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
 // Public paths/count remain in JSON; private bytes arrive only on this inherited FD.
 let count=q["keys"].as_array().unwrap().len();
 let fd=i32::try_from(q["key_bytes_fd"].as_u64().ok_or_else(||anyhow!("missing key byte FD"))?).map_err(err)?;
 ensure!(fd>2,"key byte FD must be inherited separately from stdio");
 // Linux host client only. No retained key file is opened or parsed in Rust.
 let mut channel=std::fs::File::open(format!("/proc/self/fd/{fd}")).map_err(err)?;
 let mut keys=Vec::with_capacity(count);
 for _ in 0..count {
  let mut record=[0u8;64];channel.read_exact(&mut record).map_err(err)?;
  let bytes=decode_raw_key_record(&record);
  keys.push(Keypair::try_from(bytes.as_slice()).map_err(err)?);
 }
 let mut tail=[0u8;1];ensure!(channel.read(&mut tail).map_err(err)?==0,"extra key bytes");
 let ixs:Vec<Instruction>=q["instructions"].as_array().unwrap().iter().map(|i|Instruction{program_id:Address::from_str(i["program"].as_str().unwrap()).unwrap(),accounts:i["accounts"].as_array().unwrap().iter().map(|a|AccountMeta{pubkey:Address::from_str(a[0].as_str().unwrap()).unwrap(),is_signer:a[1].as_bool().unwrap(),is_writable:a[2].as_bool().unwrap()}).collect(),data:unhex(i["data"].as_str().unwrap())}).collect();
 let conf=TransactionConfig::empty().with_priority_fee(10000).with_compute_unit_limit(1_400_000).with_loaded_accounts_data_size_limit(8*1024*1024).with_heap_size(256*1024);
 let m=Message::try_compile_with_config(&keys[0].pubkey(),&ixs,q["blockhash"].as_str().unwrap().parse().map_err(err)?,conf).map_err(err)?;
 let refs:Vec<&Keypair>=keys.iter().collect();let tx=VersionedTransaction::try_new(VersionedMessage::V1(m),&refs).map_err(err)?;
 let b=wincode::serialize(&tx).map_err(err)?;ensure!(b.len()<=4096,"TxV1 exceeds 4096 bytes");
 println!("{}",serde_json::json!({"hex":hex(&b),"signature":tx.signatures[0].to_string(),"bytes":b.len()}));Ok(())
}
fn unhex(s:&str)->Vec<u8>{(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(b:&[u8])->String{b.iter().map(|b|format!("{b:02x}")).collect()}

// Raw encoding has no content validity predicate. Fixed-size copy only; keep a
// named boundary for inspection in the exact optimized client executable.
#[inline(never)]
fn decode_raw_key_record(record:&[u8;64])->[u8;64]{*record}

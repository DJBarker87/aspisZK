//! Offline user prover. Wallet witness bytes arrive only on an inherited FD.
#[path="devnet_spend/diagnostics.rs"]
mod diagnostics;
use diagnostics::{Result,err};
#[cfg(all(not(test), not(all(target_os = "linux", panic = "abort", getrandom_backend = "linux_raw"))))]
compile_error!("build the Linux client with build-client.sh");
use serde_json::Value;
use std::io::{self,Read};
#[path="user_client/plan.rs"]
mod plan;
#[path="user_client/wallet.rs"]
mod wallet;
#[path="user_client/membership.rs"]
mod membership;
fn main()->std::process::ExitCode{
 diagnostics::initialize();
 match run(){Ok(())=>std::process::ExitCode::SUCCESS,Err(e)=>{diagnostics::report(e);std::process::ExitCode::FAILURE}}
}
fn run()->Result<()>{
 let mut s=String::new();io::stdin().read_to_string(&mut s).map_err(err)?;
 let q:Value=serde_json::from_str(&s).map_err(err)?;
 println!("{}",plan::run(&q)?);Ok(())
}
fn unhex(s:&str)->Vec<u8>{(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(b:&[u8])->String{b.iter().map(|b|format!("{b:02x}")).collect()}

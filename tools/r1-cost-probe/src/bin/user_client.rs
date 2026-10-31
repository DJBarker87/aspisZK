//! Offline user prover. Wallet witness bytes arrive only on an inherited FD.
#[path="user_client/diagnostics.rs"]
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
fn main(){
 diagnostics::initialize();
 let code=match run(){Ok(())=>0,Err(e)=>{diagnostics::report(e);1}};
 std::process::exit(code);
}
fn run()->Result<()>{
 let mut s=String::new();io::stdin().read_to_string(&mut s).map_err(err)?;
 let q:Value=serde_json::from_str(&s).map_err(err)?;
 println!("{}",plan::run(&q)?);Ok(())
}
fn unhex(s:&str)->Vec<u8>{(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn hex(b:&[u8])->String{b.iter().map(|b|format!("{b:02x}")).collect()}

// Owned projection keeps JSON indexing lifetimes at the public input boundary.
fn public_field(q:&Value,k:&str)->Value{q[k].clone()}

fn public_text(q:&Value,k:&str)->String{q[k].as_str().unwrap().to_owned()}

fn create_private_directory(dir:&std::path::Path)->Result<()>{use std::os::unix::fs::DirBuilderExt;std::fs::DirBuilder::new().mode(0o700).create(dir).map_err(err)}

fn path_join(dir:&std::path::Path,name:&str)->std::path::PathBuf{dir.join(name)}

fn client_hash()->aspis_core::HashFn{aspis_prover::HOST_HASH}

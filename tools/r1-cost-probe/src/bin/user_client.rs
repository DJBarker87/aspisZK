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
 let q:Value=parse_request(&s)?;
 let rendered=render_json(&plan::run(&q)?);print_json(rendered);Ok(())
}
fn unhex(s:&str)->Vec<u8>{let mut out=Vec::new();let mut i=0;while i<s.len(){out.push(u8::from_str_radix(&s[i..i+2],16).unwrap());i+=2;}out}
fn hex(b:&[u8])->String{let digits=b"0123456789abcdef";let mut out=Vec::with_capacity(2*b.len());let mut i=0;while i<b.len(){out.push(digits[(b[i]>>4u32) as usize]);out.push(digits[(b[i]&15) as usize]);i+=1;}String::from_utf8(out).unwrap()}

// Owned projection keeps JSON indexing lifetimes at the public input boundary.
fn public_field(q:&Value,k:&str)->Value{q[k].clone()}

fn public_text(q:&Value,k:&str)->String{q[k].as_str().unwrap().to_owned()}

fn create_private_directory(dir:&std::path::Path)->Result<()>{use std::os::unix::fs::DirBuilderExt;std::fs::DirBuilder::new().mode(0o700).create(dir).map_err(err)}

fn path_join(dir:&std::path::Path,name:&str)->std::path::PathBuf{dir.join(name)}

fn client_hash()->aspis_core::HashFn{aspis_prover::HOST_HASH}

fn triple(a:Value,b:Value,c:Value)->Vec<Value>{let mut out=Vec::with_capacity(3);out.push(a);out.push(b);out.push(c);out}

fn public_array(v:&Value)->Result<Vec<Value>>{match v.as_array(){Some(a)=>Ok(a.clone()),None=>Err(diagnostics::Error::new())}}
fn value_text(v:&Value)->Result<String>{match v.as_str(){Some(s)=>Ok(s.to_owned()),None=>Err(diagnostics::Error::new())}}

// Extraction boundaries retain actual operands rather than erased fmt Arguments.
fn wallet_fd_path(fd:i32)->String{format!("/proc/self/fd/{fd}")}
fn render_json(value:&Value)->String{format!("{}",value)}
fn print_json(mut text:String){
 use std::io::Write;
 text.push('\n');let mut output=std::io::stdout().lock();
 if output.write_all(text.as_bytes()).is_err(){panic!("client output failed");}
}
fn json_string(value:String)->Value{Value::String(value)}
fn json_array(value:Vec<Value>)->Value{Value::Array(value)}
fn json_bool(value:bool)->Value{Value::Bool(value)}
fn json_number(value:serde_json::Number)->Value{Value::Number(value)}
fn json_object(value:serde_json::Map<String,Value>)->Value{Value::Object(value)}
fn json_into_array(value:Value)->Result<Vec<Value>>{match value{Value::Array(a)=>Ok(a),_=>Err(diagnostics::Error::new())}}

fn public_lanes(pool:solana_program::pubkey::Pubkey,master:solana_program::pubkey::Pubkey)->Vec<solana_program::pubkey::Pubkey>{
 use aspis_pool::pool_v1_pair_forest_lane_address;
 (0..8).map(|i|pool_v1_pair_forest_lane_address(&pool,&master,i).unwrap().0).collect()
}
fn parent_capacity(len:usize)->usize{len.div_ceil(2).max(1)}
fn wallet_open_channel(path:String)->Result<std::fs::File>{std::fs::File::open(path).map_err(err)}
fn wallet_read_record(channel:&mut std::fs::File)->Result<[u8;wallet::WIDTH]>{
 use std::io::Read;
 use crate::diagnostics::{anyhow,ensure};
 let mut record=[0u8;wallet::WIDTH];channel.read_exact(&mut record).map_err(err)?;
 let mut tail=[0u8;1];ensure!(channel.read(&mut tail).map_err(err)?==0,"extra wallet bytes");Ok(record)
}

fn parse_request(text:&str)->Result<Value>{serde_json::from_str(text).map_err(err)}
fn pubkey_text(value:solana_program::pubkey::Pubkey)->String{value.to_string()}

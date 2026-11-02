//! Diagnostic: exact serde_json Value Display used by user_client's println!.
#[path="/home/dombarker/project-offloads/codex-pv-uc-20261029/src/tools/r1-cost-probe/src/bin/user_client/diagnostics.rs"]
mod diagnostics;
use std::fmt::Write as _;
struct Fail;
impl std::fmt::Write for Fail {
 fn write_str(&mut self,_:&str)->std::fmt::Result {Err(std::fmt::Error)}
}
fn main(){
 diagnostics::initialize();
 let v=serde_json::Value::String("public operand".to_owned());
 let mut s=String::new();assert!(write!(&mut s,"{}",v).is_ok());
 assert_eq!(s,"\"public operand\"");
 assert!(write!(&mut Fail,"{}",v).is_err());
 // This is exactly the reached formatting call, with a fixed public operand.
 println!("{}",v);
}

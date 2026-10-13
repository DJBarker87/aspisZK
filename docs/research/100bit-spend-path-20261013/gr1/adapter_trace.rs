//! Exact native/dense trace check on the adapter measurement inputs.
use aspis_r1_cost_probe::{dense,trace,verifier};
use aspis_prover::HOST_HASH;
use aspis_statement::pool_v1::{decode_pool_v1_pair_forest_terminal_statement_v1,PoolV1PairForestTerminalStatementV1,pair_forest_semantic_terminal::r0::Public};
use sha2::{Digest,Sha256};
use serde_json::json;
fn sha(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn main(){
 assert!(!cfg!(debug_assertions));let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),6);
 let mut results=vec![];
 for (name,pi,xi) in [("transfer",2,3),("withdrawal",4,5)] {
  let p=std::fs::read(&a[pi]).unwrap();let x=std::fs::read(&a[xi]).unwrap();let statement=decode_pool_v1_pair_forest_terminal_statement_v1(&x).unwrap();
  let public=match &statement{PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public}=>Public::Transfer(public,&common.lane_transition),PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}=>Public::Withdrawal(public,&common.lane_transition)};
  trace::take();let cp=verifier::tx1(public,&x,&p,10,HOST_HASH,None).unwrap();let t1=trace::take();
  verifier::tx2(&x,&p,&cp,HOST_HASH,None).unwrap();let mut t2=trace::take();
  verifier::tx2_authenticated(&x,&p,&cp,HOST_HASH,None).unwrap();let mut auth=trace::take();t2.sort();auth.sort();assert_eq!(t2,auth);
  let mut whole=t1;whole.extend(t2.clone());whole.sort();dense::verify(public,&p,HOST_HASH).unwrap();let mut oracle=trace::take();oracle.sort();assert_eq!(whole,oracle);
  let bytes:Vec<_>=whole.iter().flat_map(|(t,i,b)|t.to_le_bytes().into_iter().chain((*i as u32).to_le_bytes()).chain(*b)).collect();
  results.push(json!({"fixture":name,"proof_sha256":sha(&p),"public_sha256":sha(&x),"native_dense_equal":true,"strict_authenticated_equal":true,"trace_entries":whole.len(),"tx2_trace_entries":t2.len(),"trace_sha256":sha(&bytes),"checkpoint_sha256":sha(&cp)}));
 }
 let out=std::path::Path::new(&a[1]);assert!(!out.exists());std::fs::write(out,serde_json::to_string_pretty(&json!({"fixtures":results})).unwrap()+"\n").unwrap();
}

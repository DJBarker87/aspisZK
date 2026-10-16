//! Actual saved S2 execution; only configured failure hooks/checkpoint Result adapter are synthetic.
use super::*;
use sha2::{Digest,Sha256};
use std::cell::RefCell;
const PROOF:&[u8]=include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin"));
const PUBLIC:&[u8]=include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-public-asf8.bin"));
#[derive(Clone,Copy,Debug,PartialEq,Eq,Default)]
enum Fault { #[default] None, Geometry, Query(usize), Checkpoint }
#[derive(Clone,Debug,PartialEq,Eq,Default)]
struct Log { fault:Fault, geometry:Vec<(usize,usize,[u32;22])>, queries:Vec<(usize,Vec<u8>)>, checkpoints:Vec<Vec<u8>>, phases:Vec<Phase>, digests:Vec<(Vec<Vec<u8>>,[u8;32])> }
std::thread_local! {static LOG:RefCell<Log>=RefCell::new(Log::default());}
fn k_bytes(value:K)->[u8;16] {let mut bytes=[0;16];value.write_le_bytes(&mut bytes);bytes}
fn state(p:&Prepared,a:&Accumulator)->Vec<u8> {
 let mut b=alloc::vec![p.variant.tag()];for root in p.roots {b.extend_from_slice(&root);}
 for x in [p.gamma,p.kappa,p.alpha[0],p.alpha[1]] {b.extend_from_slice(&x.to_le_bytes());}
 b.extend_from_slice(&k_bytes(p.rho));for x in p.queries {b.extend_from_slice(&x.to_le_bytes());}
 for x in p.semantic_alpha {b.extend_from_slice(&k_bytes(x));}for z in p.z {b.extend_from_slice(&k_bytes(z.x));b.extend_from_slice(&k_bytes(z.y));}
 b.extend_from_slice(&p.claim.to_le_bytes());b.extend_from_slice(&p.state);b.extend_from_slice(&(a.next as u64).to_le_bytes());
 b.extend_from_slice(&a.rhs.to_le_bytes());b.extend_from_slice(&k_bytes(a.power));for x in &a.weights {b.extend_from_slice(&k_bytes(*x));}b
}
pub(crate) fn before_geometry(q:&[u32;22],start:usize,end:usize)->bool {
 LOG.with(|s| {let mut s=s.borrow_mut();s.geometry.push((start,end,*q));s.fault==Fault::Geometry})
}
pub(crate) fn before_query(p:&Prepared,a:&Accumulator)->bool {
 LOG.with(|s| {let mut s=s.borrow_mut();s.queries.push((a.next,state(p,a)));s.fault==Fault::Query(a.next)})
}
pub(crate) fn checkpoint_result<H:Digest32>(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:H)->Result<Vec<u8>,Error> {
 let fail=LOG.with(|s| {let mut s=s.borrow_mut();s.checkpoints.push(state(p,a));s.fault==Fault::Checkpoint});
 if fail {Err(Error::Checkpoint)} else {Ok(checkpoint(p,a,proof,public,hash))}
}
#[derive(Clone,Copy)]struct RecordedSha;
impl Digest32 for RecordedSha {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut h=Sha256::new();for p in parts {h.update(p);}let out:[u8;32]=h.finalize().into();
  LOG.with(|s|s.borrow_mut().digests.push((parts.iter().map(|x|x.to_vec()).collect(),out)));out
 }
}
fn observer(p:Phase){LOG.with(|s|s.borrow_mut().phases.push(p));}
#[derive(Clone,Debug,PartialEq,Eq)]struct Outcome { result:Result<Vec<u8>,Error>, log:Log, values:Vec<(u16,usize,[u8;32])> }
fn run(old:bool,fault:Fault)->Outcome {
 let statement=aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap();
 let public=aspis_prover::r0_fixture::statement_public(&statement);
 LOG.with(|s|*s.borrow_mut()=Log{fault,..Log::default()});let _=crate::trace::take();
 let result=if old {migration_old_tx1(public,PUBLIC,PROOF,22,RecordedSha,Some(observer))}else{tx1(public,PUBLIC,PROOF,22,RecordedSha,Some(observer))};
 Outcome {result,log:LOG.with(|s|s.borrow().clone()),values:crate::trace::take()}
}
#[test]
fn tx1_saved_s2_exact_old_new_faults_and_success() {
 assert_eq!(&PROOF[..8],b"R1P3COST");assert_eq!(PROOF[8],Variant::S2.tag());
 let success=run(true,Fault::None);assert!(success.result.is_ok(),"saved S2 old tx1 must succeed");
 assert_eq!(success.log.phases.last(),Some(&Phase::CheckpointWrite));
 assert_eq!(success.log.queries.iter().map(|x|x.0).collect::<Vec<_>>(),(0..22).collect::<Vec<_>>());
 let prepare_cut=success.log.phases.iter().position(|x|*x==Phase::Prepare).unwrap()+1;
 let last_query_cut=success.log.phases.iter().position(|x|*x==Phase::Merkle(21)).unwrap();
 for fault in [Fault::None,Fault::Geometry,Fault::Query(0),Fault::Query(21),Fault::Checkpoint] {
  let old=run(true,fault);let new=run(false,fault);assert_eq!(old,new,"fault={fault:?}");
  let expected_error=match fault {Fault::None=>None,Fault::Checkpoint=>Some(Error::Checkpoint),_=>Some(Error::Query)};
  assert_eq!(old.result.as_ref().err().copied(),expected_error);
  let cut=match fault {Fault::None=>success.log.phases.len(),Fault::Geometry|Fault::Query(0)=>prepare_cut,Fault::Query(21)=>last_query_cut,Fault::Checkpoint=>success.log.phases.len()-1,Fault::Query(_)=>unreachable!("only query 0 and 21 are configured")};
  assert_eq!(old.log.phases,&success.log.phases[..cut]);
  assert_eq!(old.values,&success.values[..old.values.len()]);assert_eq!(old.log.digests,&success.log.digests[..old.log.digests.len()]);
  assert_eq!(old.log.geometry.len(),1);
  assert_eq!(old.log.queries.len(),match fault {Fault::Geometry=>0,Fault::Query(0)=>1,_=>22});
  assert_eq!(old.log.checkpoints.len(),if matches!(fault,Fault::None|Fault::Checkpoint){1}else{0});
  std::println!("TX1_REAL_S2_CASE fault={fault:?} detail_phases={} old_new_equal=true {old:?}",cfg!(feature="detail-phases"));
 }
 std::println!("TX1_REAL_S2_PASS cases=5 k=22 first_query=0 last_query=21 synthetic_failures=4 success_controls=1");
}

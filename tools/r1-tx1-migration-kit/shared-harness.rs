//! Exact whole source bodies against shared synthetic interfaces, not production proof acceptance.
mod old {include!("shared/old.rs");}
mod new {include!("shared/new.rs");}
mod shared {
 use std::cell::RefCell;
 pub use std::{boxed::Box,vec::Vec};
 pub type E=u64;
 pub type Public<'a>=&'a[u8];
 #[derive(Clone,Copy,Debug,PartialEq,Eq)]pub enum Error {Parse,Semantic,Query,Checkpoint}
 #[derive(Clone,Copy,Debug,PartialEq,Eq)]pub enum Variant {S1,S2,D}
 impl Variant {pub fn tag(self)->u8{match self{Self::S1=>1,Self::S2=>2,Self::D=>3}}}
 #[derive(Clone,Copy,Debug,PartialEq,Eq)]pub enum Phase {Parsed,Semantic,SemanticPart(u8),Prepare,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite}
 pub type Observer=Option<fn(Phase)>;
 #[derive(Clone,Copy,Debug,PartialEq,Eq)]pub enum Fault {None,Geometry,Query(usize),Checkpoint}
 #[derive(Clone,Debug,PartialEq,Eq)]pub struct Log {pub fault:Fault,pub detailed:bool,pub phases:Vec<Phase>,pub marks:Vec<Phase>,pub values:Vec<(u16,usize,u64)>,pub calls:Vec<String>,pub digests:Vec<(Vec<Vec<u8>>,[u8;32])>}
 impl Default for Log {fn default()->Self{Self{fault:Fault::None,detailed:false,phases:vec![],marks:vec![],values:vec![],calls:vec![],digests:vec![]}}}
 std::thread_local!{static LOG:RefCell<Log>=RefCell::new(Log::default());}
 pub fn reset(fault:Fault,detailed:bool){LOG.with(|s|*s.borrow_mut()=Log{fault,detailed,..Log::default()});}
 pub fn take()->Log{LOG.with(|s|s.borrow().clone())}
 fn event(s:String){LOG.with(|l|l.borrow_mut().calls.push(s));}
 fn value(tag:u16,i:usize,v:u64){LOG.with(|l|l.borrow_mut().values.push((tag,i,v)));}
 pub fn observer(p:Phase){LOG.with(|s|s.borrow_mut().phases.push(p));}
 pub fn mark(obs:Observer,p:Phase){LOG.with(|s|s.borrow_mut().marks.push(p));if let Some(f)=obs{f(p);}}
 pub trait Digest32:Copy {fn digest(&self,parts:&[&[u8]])->[u8;32];}
 #[derive(Clone,Copy)]pub struct RecordedDigest;
 impl Digest32 for RecordedDigest {fn digest(&self,parts:&[&[u8]])->[u8;32]{
  // A deterministic shared interface, deliberately not asserted to be SHA or the production sampler.
  let mut out=[0u8;32];let mut at=0;for p in parts {for b in *p{out[at%32]=out[at%32].wrapping_mul(31).wrapping_add(*b);at+=1;}}
  LOG.with(|s|s.borrow_mut().digests.push((parts.iter().map(|x|x.to_vec()).collect(),out)));out
 }}
 pub struct Transcript {state:[u8;32]}
 impl Transcript {pub fn state(&self)->[u8;32]{self.state}}
 pub struct Sem<H:Digest32>{pub transcript:Transcript,pub hash:H}
 pub fn semantic<H:Digest32>(public:Public<'_>,bytes:&[u8],hash:H,obs:Observer)->Result<Sem<H>,Error>{
  event(format!("semantic:{public:?}:{bytes:?}"));
  for i in 0..6 {if LOG.with(|l|l.borrow().detailed){mark(obs,Phase::SemanticPart(i));}value(1,i as usize,10+i as u64);}
  Ok(Sem{transcript:Transcript{state:hash.digest(&[b"shared-semantic",public,bytes])},hash})
 }
 pub struct View<'a>{pub variant:Variant,pub semantic:&'a[u8]}
 impl<'a> View<'a>{pub fn parse(proof:&'a[u8])->Result<Self,Error>{
  event(format!("parse:{proof:?}"));let variant=match proof.first(){Some(1)=>Variant::S1,Some(2)=>Variant::S2,Some(3)=>Variant::D,_=>return Err(Error::Parse)};Ok(Self{variant,semantic:&proof[1..]})
 }}
 pub struct Prepared{pub variant:Variant,pub gamma:E,pub queries:[u32;22],pub state:[u8;32]}
 impl Prepared {pub fn new<H:Digest32>(sem:&Sem<H>,v:&View<'_>,hash:H)->Result<Box<Self>,Error>{
  event(format!("prepare:{}",v.variant.tag()));let state=hash.digest(&[b"shared-prepare",&sem.transcript.state(),&[v.variant.tag()]]);
  value(4,27,state[0] as u64);Ok(Box::new(Self{variant:v.variant,gamma:state[0] as u64,queries:core::array::from_fn(|i|100+i as u32),state}))
 }}
 pub struct Accumulator{pub next:usize,pub rhs:u64}
 impl Accumulator {pub fn new(v:Variant)->Result<Self,Error>{event(format!("accumulator:{}",v.tag()));Ok(Self{next:0,rhs:0})}}
 pub fn powers<const N:usize>(v:E)->[E;N]{core::array::from_fn(|i|v.wrapping_add(i as u64))}
 pub struct QueryGeometry;
 impl QueryGeometry {pub fn for_range(q:&[u32;22],start:usize,end:usize)->Result<Self,Error>{
  event(format!("geometry:{start}:{end}:{q:?}"));if LOG.with(|l|l.borrow().fault==Fault::Geometry){return Err(Error::Query);}Ok(Self)
 }}
 pub fn query_with_geometry<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer,_geometry:&QueryGeometry)->Result<(),Error>{
  event(format!("query:{}:{}:{}:{g:?}",v.variant.tag(),a.next,a.rhs));if LOG.with(|l|l.borrow().fault==Fault::Query(a.next)){return Err(Error::Query);}
  let i=a.next;let answer=hash.digest(&[b"shared-query",&p.state,&(i as u64).to_le_bytes()]);mark(obs,Phase::Merkle(i));
  if LOG.with(|l|l.borrow().detailed){for j in 0..3{mark(obs,Phase::QueryPart(i,j));}}
  a.rhs=a.rhs.wrapping_add(answer[0] as u64);value(11,i,a.rhs);a.next+=1;mark(obs,Phase::Query(i));Ok(())
 }
 pub fn checkpoint_result<H:Digest32>(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:H)->Result<Vec<u8>,Error>{
  event(format!("checkpoint:{}:{}:{}",p.variant.tag(),a.next,a.rhs));if LOG.with(|l|l.borrow().fault==Fault::Checkpoint){return Err(Error::Checkpoint);}
  let mut b=vec![p.variant.tag(),a.next as u8];b.extend_from_slice(&p.state);b.extend_from_slice(&a.rhs.to_le_bytes());b.extend_from_slice(&hash.digest(&[proof,public,&b]));Ok(b)
 }
}
mod r1_semantic {pub use crate::shared::semantic as verify_observed;}
#[cfg(test)]mod tests {
 use super::shared::*;
 #[derive(Clone,Debug,PartialEq,Eq)]struct Outcome {result:Result<Vec<u8>,Error>,log:Log}
 fn run(old:bool,variant:Variant,fault:Fault,detailed:bool)->Outcome{
  reset(fault,detailed);let proof=[variant.tag(),7,9];let public=[13,17];
  let result=if old{super::old::tx1(&public,&public,&proof,22,RecordedDigest,Some(observer))}else{super::new::tx1(&public,&public,&proof,22,RecordedDigest,Some(observer))};Outcome{result,log:take()}
 }
 #[test]fn tx1_exact_bodies_shared_interfaces(){
  for detailed in [false,true]{for variant in [Variant::S1,Variant::S2,Variant::D]{
   let success=run(true,variant,Fault::None,detailed);assert!(success.result.is_ok());assert_eq!(success.log.phases.last(),Some(&Phase::CheckpointWrite));
   let prepare=success.log.phases.iter().position(|p|*p==Phase::Prepare).unwrap()+1;let last=success.log.phases.iter().position(|p|*p==Phase::Merkle(21)).unwrap();
   for fault in [Fault::None,Fault::Geometry,Fault::Query(0),Fault::Query(21),Fault::Checkpoint]{
    let old=run(true,variant,fault,detailed);let new=run(false,variant,fault,detailed);assert_eq!(old,new,"{variant:?} {fault:?} detailed={detailed}");
    assert_eq!(old.result.as_ref().err().copied(),match fault{Fault::None=>None,Fault::Checkpoint=>Some(Error::Checkpoint),_=>Some(Error::Query)});
    let cut=match fault{Fault::None=>success.log.phases.len(),Fault::Geometry|Fault::Query(0)=>prepare,Fault::Query(21)=>last,Fault::Checkpoint=>success.log.phases.len()-1};
    assert_eq!(old.log.phases,&success.log.phases[..cut]);assert_eq!(old.log.marks,old.log.phases);
    assert_eq!(old.log.values,&success.log.values[..old.log.values.len()]);assert_eq!(old.log.digests,&success.log.digests[..old.log.digests.len()]);
    println!("TX1_SHARED_CASE variant={variant:?} fault={fault:?} detailed={detailed} old_new_equal=true {old:?}");
   }
  }}
  println!("TX1_SHARED_PASS cases=30 variants=3 observer_modes=2 faults_per_variant=4 success_controls=6 k=22 first_query=0 last_query=21");
 }
}

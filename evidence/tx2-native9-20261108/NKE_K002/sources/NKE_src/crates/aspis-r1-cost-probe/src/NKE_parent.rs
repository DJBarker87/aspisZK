use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn any_e()->E{let w:[u32;8]=kani::any();E::new(k([w[0],w[1],w[2],w[3]]),k([w[4],w[5],w[6],w[7]]))}
fn error(n:u8)->Error{match n%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn prepared()->Prepared{Prepared{variant:Variant::S2,roots:kani::any(),gamma:any_e(),kappa:any_e(),alpha:[any_e(),any_e()],rho:k(kani::any()),queries:kani::any(),semantic_alpha:core::array::from_fn(|_|k(kani::any())),z:[SecureCirclePoint{x:k(kani::any()),y:k(kani::any())},SecureCirclePoint{x:k(kani::any()),y:k(kani::any())}],claim:any_e(),state:kani::any()}}
struct FinishLog<'a>{proof:&'a[u8],prepared:&'a Prepared,rhs:E,power:K,next:usize,weights:*const K,cap:usize,len:usize,inactive:E,reply:Result<(),Error>,calls:usize}
impl FinishLog<'_>{fn finish(&mut self,v:&View,p:&Prepared,a:&Accumulator)->Result<(),Error>{
 self.calls+=1;
 assert!(v.variant==Variant::S2);assert!(v.semantic.is_empty());assert!(v.y1.is_empty());assert!(v.query_bytes.is_empty());assert!(v.folded_root.is_none());assert_eq!(v.inactive,self.inactive);
 assert_eq!(v.round0.as_ptr(),self.proof.as_ptr().wrapping_add(7527));assert_eq!(v.round0.len(),224);
 assert_eq!(v.round1.as_ptr(),self.proof.as_ptr().wrapping_add(7783));assert_eq!(v.round1.len(),224);
 assert_eq!(v.final_message.as_ptr(),self.proof.as_ptr().wrapping_add(8007));assert_eq!(v.final_message.len(),2048);
 let i:usize=kani::any();kani::assume(i<224);let j:usize=kani::any();kani::assume(j<2048);
 assert_eq!(v.round0[i],self.proof[7527+i]);assert_eq!(v.round1[i],self.proof[7783+i]);assert_eq!(v.final_message[j],self.proof[8007+j]);
 assert_eq!(p as *const Prepared,self.prepared as *const Prepared);
 assert_eq!(p.roots,self.prepared.roots);assert_eq!(p.gamma,self.prepared.gamma);assert_eq!(p.kappa,self.prepared.kappa);assert_eq!(p.alpha,self.prepared.alpha);assert_eq!(p.rho,self.prepared.rho);assert_eq!(p.queries,self.prepared.queries);assert_eq!(p.semantic_alpha,self.prepared.semantic_alpha);assert_eq!(p.claim,self.prepared.claim);assert_eq!(p.state,self.prepared.state);
 assert_eq!(p.z[0].x,self.prepared.z[0].x);assert_eq!(p.z[0].y,self.prepared.z[0].y);assert_eq!(p.z[1].x,self.prepared.z[1].x);assert_eq!(p.z[1].y,self.prepared.z[1].y);
 assert_eq!(a.weights.as_ptr(),self.weights);assert_eq!(a.weights.capacity(),self.cap);assert_eq!(a.weights.len(),self.len);assert_eq!(a.rhs,self.rhs);assert_eq!(a.power,self.power);assert_eq!(a.next,self.next);
 self.reply
}}
// Exact tx2_common tail following the already certified flush, with only the
// finish child changed to a full-Result local logging oracle. No observer value
// is inspected; deployed None phase effects are erased on the Lean side.
fn finish_tail(proof:&[u8],p:&Prepared,a:Accumulator,inactive:E,log:&mut FinishLog)->Result<(),Error>{
 let v=View{variant:Variant::S2,semantic:&[],y1:&[],inactive,round0:&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],folded_root:None,round1:&proof[compact::OFF_ROUND1..compact::OFF_FINAL],final_message:&proof[compact::OFF_FINAL..compact::OFF_OPENINGS],query_bytes:&[]};
 log.finish(&v,p,&a)
}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn finish_call(){
 let proof:[u8;57607]=kani::any();let len:usize=kani::any();kani::assume(len>=10055&&len<=57607);let proof=&proof[..len];
 let p=prepared();let before:[[u32;4];64]=kani::any();let mut weights=alloc::vec::Vec::with_capacity(64);for w in before{weights.push(k(w));}
 let rhs=any_e();let power=k(kani::any());let next:usize=kani::any();let inactive=any_e();let reply=if kani::any(){Ok(())}else{Err(error(kani::any()))};
 let mut log=FinishLog{proof,prepared:&p,rhs,power,next,weights:weights.as_ptr(),cap:weights.capacity(),len:64,inactive,reply,calls:0};
 let a=Accumulator{weights,rhs,power,next};let out=finish_tail(proof,&p,a,inactive,&mut log);
 assert_eq!(log.calls,1);assert_eq!(out,if cfg!(NKE_invert){match reply{Ok(())=>Err(Error::Parse),Err(_)=>Ok(())}}else{reply});
}

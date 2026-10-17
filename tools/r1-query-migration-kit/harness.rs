use super::*;
use alloc::{format, string::String, vec::Vec};
use sha2::{Digest, Sha256};
use std::{cell::RefCell, panic::{catch_unwind, AssertUnwindSafe}};
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum Fault { None, Abort(usize), Alter(usize), Decoder }
#[derive(Clone,Debug,PartialEq,Eq)] struct Event { parts:Vec<Vec<u8>>, answer:Option<[u8;32]> }
#[derive(Clone,Debug,PartialEq,Eq)] struct DecodeEvent { blocks:[[u8;32];8], advances:[[u8;32];8], result:String }
struct Context { fault:Fault, events:Vec<Event>, decoder:Vec<DecodeEvent> }
std::thread_local! {static CTX:RefCell<Context>=RefCell::new(Context{fault:Fault::None,events:Vec::new(),decoder:Vec::new()});}
#[derive(Clone,Copy)] struct RecordedSha;
impl Digest32 for RecordedSha {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  CTX.with(|c| {let mut c=c.borrow_mut();let position=c.events.len();let copied=parts.iter().map(|p|p.to_vec()).collect();
   if c.fault==Fault::Abort(position) {c.events.push(Event{parts:copied,answer:None});std::panic::panic_any(position);}
   let mut h=Sha256::new();for p in parts {h.update(p);}let mut answer:[u8;32]=h.finalize().into();
   if c.fault==Fault::Alter(position) {answer[0]^=0x80;}
   c.events.push(Event{parts:copied,answer:Some(answer)});answer
  })
 }
}
pub(super) fn decode(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError> {
 let fault=CTX.with(|c|c.borrow().fault);
 let result=if fault==Fault::Decoder {Err(aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:0,max_draws:64})}else{aspis_core::r0_transcript::queries_from_pairs(blocks,advances)};
 CTX.with(|c|c.borrow_mut().decoder.push(DecodeEvent{blocks:*blocks,advances:*advances,result:format!("{:?}",result)}));result
}
#[derive(Debug,PartialEq,Eq)] struct Outcome { result:Option<Result<[u32;22],crate::verifier::Error>>, abort:Option<usize>,state:[u8;32],events:Vec<Event>,decoder:Vec<DecodeEvent>,trace:Vec<(u16,usize,[u8;32])> }
fn run(old:bool,state:[u8;32],row:u8,payload:&[u8],fault:Fault)->Outcome {
 let _=crate::trace::take();CTX.with(|c|*c.borrow_mut()=Context{fault,events:Vec::new(),decoder:Vec::new()});
 let mut t=Transcript{state,hash:RecordedSha};
 let result=catch_unwind(AssertUnwindSafe(||if old {t.migration_old_queries(row,payload)}else{t.queries(row,payload)}));
 let (result,abort)=match result {Ok(r)=>(Some(r),None),Err(p)=>(None,Some(*p.downcast::<usize>().expect("configured digest abort payload")))};
 let(events,decoder)=CTX.with(|c|{let mut c=c.borrow_mut();(core::mem::take(&mut c.events),core::mem::take(&mut c.decoder))});
 Outcome{result,abort,state:t.state,events,decoder,trace:crate::trace::take()}
}
fn unhex(s:&str)->Vec<u8> {(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
#[test]
fn queries_exact_old_new_all_digest_positions_and_decoder() {
 let fixture:serde_json::Value=serde_json::from_str(include_str!("query_migration_context.json")).unwrap();
 let state:[u8;32]=unhex(fixture["state_hex"].as_str().unwrap()).try_into().unwrap();let payload=unhex(fixture["payload_hex"].as_str().unwrap());
 let contexts=[("saved-S2",state,31u8,payload),("synthetic-S1",[19u8;32],30u8,alloc::vec![7u8;64]),("synthetic-D",[37u8;32],31u8,alloc::vec![11u8;512])];
 let mut cases=0;
 for(label,state,row,payload)in contexts {
  let faults=core::iter::once(Fault::None).chain((1..=16).map(Fault::Abort)).chain((1..=16).map(Fault::Alter)).chain(core::iter::once(Fault::Decoder));
  for fault in faults {
   let a=run(true,state,row,&payload,fault);let b=run(false,state,row,&payload,fault);assert_eq!(a,b,"{} {:?}",label,fault);
   match fault {
    Fault::Abort(p)=>{assert_eq!(b.abort,Some(p));assert_eq!(b.events.len(),p+1);assert_eq!(b.events.last().unwrap().answer,None);assert!(b.trace.is_empty()&&b.decoder.is_empty());assert_eq!(b.state,b.events[0].answer.unwrap());}
    Fault::Decoder=>{assert_eq!(b.result,Some(Err(crate::verifier::Error::Transcript)));assert_eq!(b.events.len(),17);assert!(b.trace.is_empty());assert_eq!(b.decoder.len(),1);assert_eq!(b.state,b.events[0].answer.unwrap());}
    Fault::None|Fault::Alter(_)=>{
     if fault==Fault::None {assert!(matches!(b.result,Some(Ok(_))),"successcontrol mustdecode");}
     assert_eq!(b.events.len(),17);assert_eq!(b.decoder.len(),1);
     if let Some(Ok(q))=b.result {assert_eq!(b.trace.len(),22);for i in 0..22 {assert_eq!(b.trace[i],(5,i,E::from_m31(aspis_core::field::M31(q[i])).to_le_bytes()));}
      let decoded=aspis_core::r0_transcript::queries_from_pairs(&b.decoder[0].blocks,&b.decoder[0].advances).unwrap();assert_eq!(decoded.0,q);assert_eq!(decoded.1,b.state);
     }else{assert!(b.trace.is_empty());}
    }
   }
   if label=="saved-S2"&&fault==Fault::None {
    assert_eq!(unhex(fixture["expected_absorbed_state"].as_str().unwrap()),b.events[0].answer.unwrap());
    let expected=fixture["expected17calls"].as_array().unwrap();assert_eq!(expected.len(),b.events.len());
    for (e,v)in b.events.iter().zip(expected) {let parts:Vec<Vec<u8>>=v["parts_hex"].as_array().unwrap().iter().map(|p|unhex(p.as_str().unwrap())).collect();assert_eq!(parts,e.parts);assert_eq!(unhex(v["output_hex"].as_str().unwrap()),e.answer.unwrap());}
   }
   std::println!("QUERY_MIGRATION_CASE {}",serde_json::json!({"context":label,"fault":format!("{:?}",fault),"result":format!("{:?}",b.result),"abort":b.abort,"state":b.state.to_vec(),"events":b.events.iter().map(|e|serde_json::json!({"parts":e.parts,"answer":e.answer.map(|a|a.to_vec())})).collect::<Vec<_>>(),"decoder":format!("{:?}",b.decoder),"trace":b.trace.iter().map(|(t,i,v)|serde_json::json!([t,i,v.to_vec()])).collect::<Vec<_>>()}));cases+=1;
  }
 }
 assert_eq!(cases,102);std::println!("QUERY_MIGRATION_PASS cases=102 contexts=3 digest_abort_cases=48 altered_digest_cases=48 decoder_errors=3 success_controls=3 trace_indices=0..21");
}

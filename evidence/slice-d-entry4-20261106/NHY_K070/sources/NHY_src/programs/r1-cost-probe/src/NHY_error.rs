//! Deployed Debug callback instantiated separately at each label, String writer.
use super::*;
use core::fmt::Write;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn parse_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Parse).unwrap();
 let expected=b"r1:error:Parse";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(parse_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse(){parse_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn parse_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Parse).unwrap();
 let expected=b"r1:error:Parse";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(parse_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse_wrong(){parse_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn semantic_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Semantic).unwrap();
 let expected=b"r1:error:Semantic";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(semantic_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn semantic(){semantic_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn semantic_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Semantic).unwrap();
 let expected=b"r1:error:Semantic";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(semantic_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn semantic_wrong(){semantic_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn transcript_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Transcript).unwrap();
 let expected=b"r1:error:Transcript";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(transcript_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn transcript(){transcript_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn transcript_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Transcript).unwrap();
 let expected=b"r1:error:Transcript";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(transcript_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn transcript_wrong(){transcript_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn relation_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Relation).unwrap();
 let expected=b"r1:error:Relation";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(relation_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn relation(){relation_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn relation_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Relation).unwrap();
 let expected=b"r1:error:Relation";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(relation_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn relation_wrong(){relation_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn merkle_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Merkle).unwrap();
 let expected=b"r1:error:Merkle";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(merkle_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn merkle(){merkle_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn merkle_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Merkle).unwrap();
 let expected=b"r1:error:Merkle";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(merkle_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn merkle_wrong(){merkle_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn query_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Query).unwrap();
 let expected=b"r1:error:Query";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(query_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn query(){query_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn query_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Query).unwrap();
 let expected=b"r1:error:Query";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(query_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn query_wrong(){query_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn checkpoint_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Checkpoint).unwrap();
 let expected=b"r1:error:Checkpoint";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(checkpoint_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint(){checkpoint_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn checkpoint_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Checkpoint).unwrap();
 let expected=b"r1:error:Checkpoint";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(checkpoint_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_wrong(){checkpoint_wrong_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn allocation_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Allocation).unwrap();
 let expected=b"r1:error:Allocation";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(allocation_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation(){allocation_packet();}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn allocation_wrong_packet()->bool{
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 write!(&mut w,"{:?}",verifier::Error::Allocation).unwrap();
 let expected=b"r1:error:Allocation";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(allocation_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation_wrong(){allocation_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn writer_parse_packet()->bool {
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 core::fmt::Write::write_str(&mut *w,"Parse").unwrap();
 let expected=b"r1:error:Parse";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])
}
#[kani::proof_for_contract(writer_parse_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn writer_parse(){writer_parse_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn writer_parse_wrong_packet()->bool {
 let mut w=core::mem::ManuallyDrop::new(String::with_capacity(24));w.push_str("r1:error:");
 core::fmt::Write::write_str(&mut *w,"Parse").unwrap();
 let expected=b"r1:error:Parse";let j:usize=kani::any();kani::assume(j<expected.len());
 (w.len()==expected.len()&&w.as_bytes()[j]==expected[j])==false
}
#[kani::proof_for_contract(writer_parse_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn writer_parse_wrong(){writer_parse_wrong_packet();}

// Per-label Debug callback cut: observe the actual write_str argument without
// copying it into a custom buffer or invoking String allocation/growth.
struct DebugLog {count:u8,expected:&'static str,exact:bool,length:usize}
impl core::fmt::Write for DebugLog {
 fn write_str(&mut self,s:&str)->core::fmt::Result {self.count+=1;self.length=s.len();self.exact=s==self.expected;Ok(())}
}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_parse_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Parse",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Parse).unwrap();
 
 log.count==1&&log.exact&&log.length==5
}
#[kani::proof_for_contract(callback_parse_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_parse(){callback_parse_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_parse_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Parse",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Parse).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==5
}
#[kani::proof_for_contract(callback_parse_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_parse_wrong(){callback_parse_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_semantic_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Semantic",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Semantic).unwrap();
 
 log.count==1&&log.exact&&log.length==8
}
#[kani::proof_for_contract(callback_semantic_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_semantic(){callback_semantic_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_semantic_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Semantic",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Semantic).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==8
}
#[kani::proof_for_contract(callback_semantic_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_semantic_wrong(){callback_semantic_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_transcript_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Transcript",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Transcript).unwrap();
 
 log.count==1&&log.exact&&log.length==10
}
#[kani::proof_for_contract(callback_transcript_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_transcript(){callback_transcript_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_transcript_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Transcript",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Transcript).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==10
}
#[kani::proof_for_contract(callback_transcript_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_transcript_wrong(){callback_transcript_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_relation_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Relation",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Relation).unwrap();
 
 log.count==1&&log.exact&&log.length==8
}
#[kani::proof_for_contract(callback_relation_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_relation(){callback_relation_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_relation_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Relation",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Relation).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==8
}
#[kani::proof_for_contract(callback_relation_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_relation_wrong(){callback_relation_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_merkle_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Merkle",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Merkle).unwrap();
 
 log.count==1&&log.exact&&log.length==6
}
#[kani::proof_for_contract(callback_merkle_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_merkle(){callback_merkle_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_merkle_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Merkle",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Merkle).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==6
}
#[kani::proof_for_contract(callback_merkle_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_merkle_wrong(){callback_merkle_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_query_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Query",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Query).unwrap();
 
 log.count==1&&log.exact&&log.length==5
}
#[kani::proof_for_contract(callback_query_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_query(){callback_query_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_query_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Query",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Query).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==5
}
#[kani::proof_for_contract(callback_query_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_query_wrong(){callback_query_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_checkpoint_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Checkpoint",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Checkpoint).unwrap();
 
 log.count==1&&log.exact&&log.length==10
}
#[kani::proof_for_contract(callback_checkpoint_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_checkpoint(){callback_checkpoint_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_checkpoint_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Checkpoint",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Checkpoint).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==10
}
#[kani::proof_for_contract(callback_checkpoint_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_checkpoint_wrong(){callback_checkpoint_wrong_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_allocation_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Allocation",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Allocation).unwrap();
 
 log.count==1&&log.exact&&log.length==10
}
#[kani::proof_for_contract(callback_allocation_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_allocation(){callback_allocation_packet();}

#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_allocation_wrong_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Allocation",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Allocation).unwrap();
 log.exact=!log.exact;
 log.count==1&&log.exact&&log.length==10
}
#[kani::proof_for_contract(callback_allocation_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_allocation_wrong(){callback_allocation_wrong_packet();}

// Ruling(al) documented stability companion, no changed assertion/domain.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn callback_parse_stability_packet()->bool{
 let mut log=DebugLog{count:0,expected:"Parse",exact:false,length:0};
 write!(&mut log,"{:?}",verifier::Error::Parse).unwrap();
 
 log.count==1&&log.exact&&log.length==5
}
#[kani::proof_for_contract(callback_parse_stability_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn callback_parse_stability(){callback_parse_stability_packet();}


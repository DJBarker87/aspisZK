//! Isolated Debug rendering into a LOCAL fixed writer; no syscall or heap String.
use super::*;
use core::fmt::Write;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Writer {bytes:[u8;24],len:usize}
impl core::fmt::Write for Writer {
 fn write_str(&mut self,s:&str)->core::fmt::Result {
  for b in s.bytes(){if self.len==24{return Err(core::fmt::Error)};self.bytes[self.len]=b;self.len+=1;} Ok(())
 }
}
fn check(e:verifier::Error,expected:&[u8],wrong:bool){
 let mut w=Writer{bytes:[0;24],len:0};
 write!(&mut w,"r1:error:{:?}",e).unwrap();
 assert_eq!(w.len,expected.len());
 let j:usize=kani::any();kani::assume(j<w.len);
 assert!((w.bytes[j]==expected[j])!=wrong);
 for k in w.len..24 {assert_eq!(w.bytes[k],0);}
}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse(){check(verifier::Error::Parse,b"r1:error:Parse",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse_wrong(){check(verifier::Error::Parse,b"r1:error:Parse",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn semantic(){check(verifier::Error::Semantic,b"r1:error:Semantic",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn semantic_wrong(){check(verifier::Error::Semantic,b"r1:error:Semantic",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn transcript(){check(verifier::Error::Transcript,b"r1:error:Transcript",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn transcript_wrong(){check(verifier::Error::Transcript,b"r1:error:Transcript",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn relation(){check(verifier::Error::Relation,b"r1:error:Relation",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn relation_wrong(){check(verifier::Error::Relation,b"r1:error:Relation",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn merkle(){check(verifier::Error::Merkle,b"r1:error:Merkle",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn merkle_wrong(){check(verifier::Error::Merkle,b"r1:error:Merkle",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn query(){check(verifier::Error::Query,b"r1:error:Query",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn query_wrong(){check(verifier::Error::Query,b"r1:error:Query",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint(){check(verifier::Error::Checkpoint,b"r1:error:Checkpoint",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_wrong(){check(verifier::Error::Checkpoint,b"r1:error:Checkpoint",true);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation(){check(verifier::Error::Allocation,b"r1:error:Allocation",false);}

#[kani::proof] #[kani::unwind(25)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation_wrong(){check(verifier::Error::Allocation,b"r1:error:Allocation",true);}

fn log_parse(s:&str){let expected=b"r1:error:Parse";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_parse()->bool {matches!(error(verifier::Error::Parse),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_parse)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_parse)]
fn native_parse(){assert!(packet_parse());}

fn log_parse_wrong(s:&str){let expected=b"r1:error:Parse";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_parse_wrong()->bool {matches!(error(verifier::Error::Parse),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_parse_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_parse_wrong)]
fn native_parse_wrong(){assert!(packet_parse_wrong());}

fn log_semantic(s:&str){let expected=b"r1:error:Semantic";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_semantic()->bool {matches!(error(verifier::Error::Semantic),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_semantic)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_semantic)]
fn native_semantic(){assert!(packet_semantic());}

fn log_semantic_wrong(s:&str){let expected=b"r1:error:Semantic";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_semantic_wrong()->bool {matches!(error(verifier::Error::Semantic),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_semantic_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_semantic_wrong)]
fn native_semantic_wrong(){assert!(packet_semantic_wrong());}

fn log_transcript(s:&str){let expected=b"r1:error:Transcript";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_transcript()->bool {matches!(error(verifier::Error::Transcript),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_transcript)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_transcript)]
fn native_transcript(){assert!(packet_transcript());}

fn log_transcript_wrong(s:&str){let expected=b"r1:error:Transcript";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_transcript_wrong()->bool {matches!(error(verifier::Error::Transcript),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_transcript_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_transcript_wrong)]
fn native_transcript_wrong(){assert!(packet_transcript_wrong());}

fn log_relation(s:&str){let expected=b"r1:error:Relation";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_relation()->bool {matches!(error(verifier::Error::Relation),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_relation)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_relation)]
fn native_relation(){assert!(packet_relation());}

fn log_relation_wrong(s:&str){let expected=b"r1:error:Relation";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_relation_wrong()->bool {matches!(error(verifier::Error::Relation),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_relation_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_relation_wrong)]
fn native_relation_wrong(){assert!(packet_relation_wrong());}

fn log_merkle(s:&str){let expected=b"r1:error:Merkle";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_merkle()->bool {matches!(error(verifier::Error::Merkle),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_merkle)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_merkle)]
fn native_merkle(){assert!(packet_merkle());}

fn log_merkle_wrong(s:&str){let expected=b"r1:error:Merkle";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_merkle_wrong()->bool {matches!(error(verifier::Error::Merkle),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_merkle_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_merkle_wrong)]
fn native_merkle_wrong(){assert!(packet_merkle_wrong());}

fn log_query(s:&str){let expected=b"r1:error:Query";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_query()->bool {matches!(error(verifier::Error::Query),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_query)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_query)]
fn native_query(){assert!(packet_query());}

fn log_query_wrong(s:&str){let expected=b"r1:error:Query";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_query_wrong()->bool {matches!(error(verifier::Error::Query),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_query_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_query_wrong)]
fn native_query_wrong(){assert!(packet_query_wrong());}

fn log_checkpoint(s:&str){let expected=b"r1:error:Checkpoint";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_checkpoint()->bool {matches!(error(verifier::Error::Checkpoint),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_checkpoint)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_checkpoint)]
fn native_checkpoint(){assert!(packet_checkpoint());}

fn log_checkpoint_wrong(s:&str){let expected=b"r1:error:Checkpoint";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_checkpoint_wrong()->bool {matches!(error(verifier::Error::Checkpoint),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_checkpoint_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_checkpoint_wrong)]
fn native_checkpoint_wrong(){assert!(packet_checkpoint_wrong());}

fn log_allocation(s:&str){let expected=b"r1:error:Allocation";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=false);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_allocation()->bool {matches!(error(verifier::Error::Allocation),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_allocation)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_allocation)]
fn native_allocation(){assert!(packet_allocation());}

fn log_allocation_wrong(s:&str){let expected=b"r1:error:Allocation";assert_eq!(s.len(),expected.len());let j:usize=kani::any();kani::assume(j<s.len());assert!((s.as_bytes()[j]==expected[j])!=true);kani::cover!(true);}
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn packet_allocation_wrong()->bool {matches!(error(verifier::Error::Allocation),ProgramError::InvalidInstructionData)}
#[kani::proof_for_contract(packet_allocation_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_allocation_wrong)]
fn native_allocation_wrong(){assert!(packet_allocation_wrong());}

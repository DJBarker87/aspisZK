#![allow(dead_code,unexpected_cfgs)]
use aspis_r1_cost_probe::verifier;
use solana_program::{msg,program_error::ProgramError};
fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}
fn owned_error(error:verifier::Error)->ProgramError {
 let message=match error {
  verifier::Error::Parse=>"r1:error:Parse",
  verifier::Error::Semantic=>"r1:error:Semantic",
  verifier::Error::Transcript=>"r1:error:Transcript",
  verifier::Error::Relation=>"r1:error:Relation",
  verifier::Error::Merkle=>"r1:error:Merkle",
  verifier::Error::Query=>"r1:error:Query",
  verifier::Error::Checkpoint=>"r1:error:Checkpoint",
  verifier::Error::Allocation=>"r1:error:Allocation",
 };
 solana_program::log::sol_log(message);
 ProgramError::InvalidInstructionData
}
#[cfg(kani)] mod proofs {
 use super::*;
 static mut LOG:Option<Vec<u8>>=None;
 static mut CALLS:u8=0;
 fn capture(message:&str) {unsafe{assert!(LOG.is_none());LOG=Some(message.as_bytes().to_vec());CALLS+=1;}}
 #[kani::proof]
 #[kani::unwind(32)]
 #[kani::stub(solana_program::log::sol_log,capture)]
 fn actual_error_log_owned_correspondence() {
  let tag:u8=kani::any();kani::assume(tag<8);
  let error=match tag {
   0=>verifier::Error::Parse,
   1=>verifier::Error::Semantic,
   2=>verifier::Error::Transcript,
   3=>verifier::Error::Relation,
   4=>verifier::Error::Merkle,
   5=>verifier::Error::Query,
   6=>verifier::Error::Checkpoint,
   7=>verifier::Error::Allocation,
   _=>unreachable!(),
  };
  let reference=match tag {
   0=>verifier::Error::Parse,
   1=>verifier::Error::Semantic,
   2=>verifier::Error::Transcript,
   3=>verifier::Error::Relation,
   4=>verifier::Error::Merkle,
   5=>verifier::Error::Query,
   6=>verifier::Error::Checkpoint,
   7=>verifier::Error::Allocation,
   _=>unreachable!(),
  };
  unsafe{LOG=None;CALLS=0;}
  let actual=super::error(error);
  let actual_log=unsafe{LOG.take().unwrap()};assert_eq!(unsafe{CALLS},1);
  unsafe{CALLS=0;}
  let expected=owned_error(reference);
  let expected_log=unsafe{LOG.take().unwrap()};
  assert_eq!(unsafe{CALLS},1);
  assert!(matches!(actual,ProgramError::InvalidInstructionData));
  assert!(matches!(expected,ProgramError::InvalidInstructionData));
  assert_eq!(actual_log,expected_log);
  kani::cover!(tag==0,"Parse log");kani::cover!(tag==7,"Allocation log");
 }
}

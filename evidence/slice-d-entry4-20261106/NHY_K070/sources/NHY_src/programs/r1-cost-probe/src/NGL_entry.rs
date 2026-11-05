use super::*;
extern crate alloc;
#[kani::proof] #[kani::unwind(6)]
fn rejected_entry2(){let key=Pubkey::new_from_array([0;32]);let data:[u8;2]=kani::any();kani::assume(data!=[3,10]&&data!=[3,11]);let r=process_r1_cost_probe_instruction(&key,&[],&data);assert!((r==Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(6)]
fn rejected_entry2_wrong(){let key=Pubkey::new_from_array([0;32]);let data:[u8;2]=kani::any();kani::assume(data!=[3,10]&&data!=[3,11]);let r=process_r1_cost_probe_instruction(&key,&[],&data);assert!((r==Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

fn log_parse(message:&str){assert_eq!(message,"r1:error:Parse");}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_parse)]
fn error_parse(){let r=error(verifier::Error::Parse);assert_eq!(r,ProgramError::InvalidInstructionData);}

fn log_parse_wrong(message:&str){assert_eq!(message,"r1:error:Semantic");}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,log_parse_wrong)]
fn error_parse_wrong(){let r=error(verifier::Error::Parse);assert_eq!(r,ProgramError::InvalidInstructionData);}

include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));

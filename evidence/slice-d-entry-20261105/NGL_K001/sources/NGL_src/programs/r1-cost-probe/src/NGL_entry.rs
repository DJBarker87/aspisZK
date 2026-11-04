use super::*;
#[kani::proof] #[kani::unwind(6)]
fn rejected_entry2(){let key=Pubkey::new_from_array([0;32]);let data:[u8;2]=kani::any();kani::assume(data!=[3,10]&&data!=[3,11]);let r=process_r1_cost_probe_instruction(&key,&[],&data);assert!((r==Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

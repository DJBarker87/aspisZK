use aspis_s126_owned_sdk::OwnedSdk;
use solana_program::program_error::ProgramError;

pub fn copy_step(sdk:&mut OwnedSdk,slot:usize,source:&[u8],offset:usize) {
 sdk.data_cells[slot].bytes[offset]=source[offset];
}

pub fn copy_in_place(sdk:&mut OwnedSdk,slot:usize,source:&[u8])->Result<(),ProgramError> {
 if sdk.data_cells[slot].bytes.len()!=source.len() {
  return Err(ProgramError::InvalidAccountData);
 }
 let mut offset=0;
 while offset<source.len() {
  copy_step(sdk,slot,source,offset);
  offset+=1;
 }
 Ok(())
}

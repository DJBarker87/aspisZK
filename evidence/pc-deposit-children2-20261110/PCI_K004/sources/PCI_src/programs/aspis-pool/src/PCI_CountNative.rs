use super::*;
fn require_exact_account_count_fission(len: usize, expected: usize) -> ProgramResult {
    if len != expected {
        return Err(if len < expected {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    Ok(())
}
fn reference(len:usize,expected:usize)->ProgramResult {
 if len==expected {Ok(())}else if len<expected {Err(ProgramError::NotEnoughAccountKeys)}else{Err(ProgramError::InvalidArgument)}
}
#[kani::proof]
fn count_all_words(){
 let len:usize=kani::any();let expected:usize=kani::any();
 let result=require_exact_account_count_fission(len,expected);
 assert!((result==reference(len,expected))!=cfg!(PCI_NEG_COUNT));
}

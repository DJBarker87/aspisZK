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
// Retired whole-ProgramError equality K004 timed out. Split exhaustive comparison arms.
#[kani::proof]
fn count_all_words(){
 let len:usize=kani::any();let expected:usize=kani::any();
 #[cfg(PCI_COUNT_EQUAL)] kani::assume(len==expected);
 #[cfg(PCI_COUNT_SHORT)] kani::assume(len<expected);
 #[cfg(PCI_COUNT_LONG)] kani::assume(len>expected);
 let result=require_exact_account_count_fission(len,expected);
 #[cfg(PCI_COUNT_EQUAL)] let exact=matches!(result,Ok(()));
 #[cfg(PCI_COUNT_SHORT)] let exact=matches!(result,Err(ProgramError::NotEnoughAccountKeys));
 #[cfg(PCI_COUNT_LONG)] let exact=matches!(result,Err(ProgramError::InvalidArgument));
 assert!(exact!=cfg!(PCI_NEG_COUNT));
}

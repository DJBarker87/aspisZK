//! Real AccountInfo flag projection; runtime provenance remains the single R16 premise.
use super::{readonly_buffer_meta_ok, require_readonly_buffer};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

#[test]
fn readonly_buffer_exact_result_and_wrapper_all_flags() {
    // The helper ignores owner, key, data and balances. Check all eight flag
    // combinations through the real wrapper with unrelated key and owner values.
    for signer in [false, true] {
        for writable in [false, true] {
            for executable in [false, true] {
                let key = Pubkey::new_from_array([7; 32]);
                let owner = Pubkey::new_from_array([8; 32]);
                let mut lamports = 1;
                let mut data = [0u8; 1];
                let account = AccountInfo::new(
                    &key, signer, writable, &mut lamports, &mut data, &owner, executable, 0,
                );
                let expected = if signer || writable || executable {
                    Err(ProgramError::InvalidAccountData)
                } else {
                    Ok(())
                };
                assert_eq!(readonly_buffer_meta_ok(signer, writable, executable), expected);
                assert_eq!(require_readonly_buffer(&account), expected);
            }
        }
    }
}

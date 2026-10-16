//! Native tests of the real AccountInfo wrapper. Loader/runtime metadata
//! provenance remains a separate R16 premise and J1.R13 runtime gate.
use super::require_readonly_account;
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

fn check_wrapper(owner: [u8; 32], signer: bool, writable: bool, executable: bool, rejected: bool) {
    let expected = Pubkey::new_from_array([7; 32]);
    // Deliberately use the expected owner as the account key: checking key
    // instead of owner would incorrectly accept the wrong-owner case.
    let key = Pubkey::new_from_array([7; 32]);
    let actual_owner = Pubkey::new_from_array(owner);
    let mut lamports = 1;
    let mut data = [0u8; 1];
    let account = AccountInfo::new(
        &key, signer, writable, &mut lamports, &mut data, &actual_owner, executable, 0,
    );
    assert_eq!(
        require_readonly_account(&account, &expected),
        if rejected { Err(ProgramError::InvalidAccountData) } else { Ok(()) },
    );
}

#[test]
fn readonly_metadata_rejects_signer() {
    check_wrapper([7; 32], true, false, false, true);
}

#[test]
fn readonly_metadata_rejects_writable() {
    check_wrapper([7; 32], false, true, false, true);
}

#[test]
fn readonly_metadata_rejects_executable() {
    check_wrapper([7; 32], false, false, true, true);
}

#[test]
fn readonly_metadata_rejects_wrong_owner() {
    check_wrapper([8; 32], false, false, false, true);
}

#[test]
fn readonly_metadata_accepts_equal_owner_values() {
    // Equal owner values at separate addresses must compare equal.
    check_wrapper([7; 32], false, false, false, false);
}

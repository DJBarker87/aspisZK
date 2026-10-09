use aspis_verifier::process_spend_production_instruction;
use solana_program::{program_error::ProgramError, pubkey::Pubkey};
#[test]
fn production_rejects_r0_diagnostic_tag_before_accounts() {
    assert_eq!(
        process_spend_production_instruction(&Pubkey::new_unique(), &[], &[241]),
        Err(ProgramError::InvalidInstructionData)
    );
}

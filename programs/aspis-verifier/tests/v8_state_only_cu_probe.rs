use aspis_verifier::process_spend_production_instruction;
use solana_program::{program_error::ProgramError, pubkey::Pubkey};

#[test]
fn v8_diagnostic_tag_is_rejected_by_production_before_accounts() {
    let mut wire = vec![0; 217];
    wire[0] = 240;
    assert_eq!(
        process_spend_production_instruction(&Pubkey::new_unique(), &[], &wire),
        Err(ProgramError::InvalidInstructionData),
    );
}

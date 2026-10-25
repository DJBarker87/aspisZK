#![allow(non_snake_case)]
use aspis_r1_cost_probe_program::process_r1_cost_probe_instruction;
use solana_program::{account_info::AccountInfo, pubkey::Pubkey, program_error::ProgramError};

// Execute the actual shipped release entrypoint, not a fissioned guard model.
// Invalid proof/public lengths are deferred until AFTER the checkpoint gate.
fn Hist_try_initialized(split: u8, marker: u8) -> Result<(), ProgramError> {
    let program = Pubkey::new_from_array([17; 32]);
    let proof_key = Pubkey::new_from_array([18; 32]);
    let public_key = Pubkey::new_from_array([19; 32]);
    let checkpoint_key = Pubkey::new_from_array([20; 32]);
    let foreign = Pubkey::new_from_array([21; 32]);
    let mut lp = 1; let mut lu = 1; let mut lc = 1;
    let mut proof = []; let mut public = []; let mut checkpoint = [0; 1768];
    checkpoint[0] = marker;
    let expected = checkpoint;
    let result = {
        let accounts = [
            AccountInfo::new(&proof_key, false, false, &mut lp, &mut proof, &foreign, false, 0),
            AccountInfo::new(&public_key, false, false, &mut lu, &mut public, &foreign, false, 0),
            AccountInfo::new(&checkpoint_key, false, true, &mut lc, &mut checkpoint, &program, false, 0),
        ];
        process_r1_cost_probe_instruction(&program, &accounts, &[3, split])
    };
    assert_eq!(checkpoint, expected);
    assert_eq!((lp,lu,lc), (1,1,1));
    result
}

#[cfg(test)]
mod Hist_tests {
    use super::*;
    #[test]
    fn Hist_actual_entrypoint_rejects_initialized_checkpoint() {
        for split in [10, 11] {
            for marker in [1, 82, 255] {
                assert_eq!(Hist_try_initialized(split, marker), Err(ProgramError::AccountAlreadyInitialized));
            }
        }
    }
    #[test]
    fn Hist_outer_release_guard_excludes_every_lifecycle_tag() {
        let program = Pubkey::new_from_array([17; 32]);
        for tag in [1,2,4,5,6] {
            for tail in [&[][..], &[0,1,2][..], b"ASQ8".as_slice()] {
                let mut data = vec![tag]; data.extend_from_slice(tail);
                assert_eq!(process_r1_cost_probe_instruction(&program, &[], &data), Err(ProgramError::InvalidInstructionData));
            }
        }
    }
}

#[cfg(kani)]
mod Hist_proofs {
    use super::*;
    #[kani::proof]
    fn Hist_initialized_never_rewritten() {
        let marker: u8 = kani::any();
        let second_split: bool = kani::any();
        kani::assume(marker != 0);
        assert_eq!(Hist_try_initialized(if second_split {11} else {10}, marker),
            Err(ProgramError::AccountAlreadyInitialized));
        kani::cover!(marker == 82);
    }
}

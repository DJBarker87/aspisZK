
#[cfg(kani)]
mod Hir_encoded_checkpoint {
    use super::*;

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_encoded_checkpoint_cannot_reinitialize() {
        let checkpoint = PoolV1PairForestCheckpointV1 {
            bump: kani::any(),
            master: kani::any(),
            deployment_domain: kani::any(),
            checkpoint_sequence: kani::any(),
            global_root: core::array::from_fn(|_| M31(kani::any())),
            lane_sequences: kani::any(),
        };
        if let Ok(mut image) = encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint) {
            assert!(image[0] == b'A');
            let original = image;
            let id = Pubkey::new_from_array([7; 32]);
            let address = Pubkey::new_from_array([8; 32]);
            let mut lamports = u64::MAX;
            let account = AccountInfo::new(&address, false, true, &mut lamports,
                &mut image, &id, false, 0);
            assert!(require_program_owned_zeroed(&account, &id, 192, &Rent::default()).is_err());
            assert!(crate::processor::plan_fresh_program_pda(&account, &id, &address, 192).is_err());
            drop(account);
            assert!(image == original);
        }
    }
}

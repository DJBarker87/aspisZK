//! Native pure-source gates. No shipped-source modifications or stubs.
#[cfg(kani)]
mod PoolW_checks {
    use aspis_statement::pool_v1::*;
    use aspis_core::field::M31;
    fn checkpoint() -> PoolV1PairForestCheckpointV1 {
        PoolV1PairForestCheckpointV1 { bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),
            checkpoint_sequence:kani::any(),global_root:core::array::from_fn(|_|M31(kani::any())),lane_sequences:kani::any() }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolW_encode_exact_bindings() {
        let cp=checkpoint();
        if let Ok(image)=encode_pool_v1_pair_forest_checkpoint_v1(&cp) {
            assert!(image.len()==192);
            assert!(image[0..4]==*b"ASC8");assert!(image[4]==2 && image[5]==8 && image[6]==1);
            assert!(image[7]==cp.bump);
            assert!(image[8..40]==cp.master);assert!(image[40..72]==cp.deployment_domain);
            assert!(image[72..80]==cp.checkpoint_sequence.to_le_bytes());
            assert!(image[176..192]==[0u8;16]);
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolW_encode_decode_roundtrip() {
        let cp=checkpoint();
        if let Ok(image)=encode_pool_v1_pair_forest_checkpoint_v1(&cp) {
            assert!(decode_pool_v1_pair_forest_checkpoint_v1(&image)==Ok(cp));
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolW_decode_encode_canonical() {
        let image:[u8;192]=kani::any();
        if let Ok(cp)=decode_pool_v1_pair_forest_checkpoint_v1(&image) {
            assert!(encode_pool_v1_pair_forest_checkpoint_v1(&cp)==Ok(image));
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolW_encode_selected_sequence() {
        let cp=checkpoint();let lane:usize=kani::any();kani::assume(lane<8);
        if let Ok(image)=encode_pool_v1_pair_forest_checkpoint_v1(&cp) {
            let start=112+8*lane;
            assert!(image[start..start+8]==cp.lane_sequences[lane].to_le_bytes());
        }
    }
}

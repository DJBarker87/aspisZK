    fn PCD_digest() -> [aspis_core::field::M31;8] {
        [aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any()),aspis_core::field::M31(kani::any())]
    }
    fn PCD_lane(next: u64) -> PoolV1PairForestLaneStateV1 {
        PoolV1PairForestLaneStateV1 {
            master: kani::any(), bump: kani::any(), lane_id: kani::any(),
            tree: IncrementalMerkleTreeV1 { next_leaf_index: next,
                root: PCD_digest(), frontier: [PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest()] }
        }
    }
    fn PCD_result(next: u64) -> aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1 {
        aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1 {
            transition_kind: if kani::any() { aspis_statement::pool_v1::PoolV1TransitionKind::PrivateTransfer }
                             else { aspis_statement::pool_v1::PoolV1TransitionKind::Withdrawal },
            master_account: kani::any(), selected_lane_account: kani::any(), output_lane: kani::any(),
            nullifier: PCD_digest(), verified_afterstate: aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next, next_root: PCD_digest(), next_frontier: [PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest(),PCD_digest()] }
        }
    }
    #[kani::proof_for_contract(super::next_pair_forest_lane_v1)]
    fn PCD_checked_rejection_contract() {
        let old: u64 = kani::any(); let next: u64 = kani::any();
        kani::assume(old.checked_add(1) != Some(next));
        let lane = PCD_lane(old); let result = PCD_result(next);
        let _ = super::next_pair_forest_lane_v1(&lane, &result);
    }
    #[kani::proof]
    fn PCD_checked_rejection_control() {
        let old: u64 = kani::any(); let next: u64 = kani::any();
        kani::assume(old.checked_add(1) != Some(next));
        let lane = PCD_lane(old); let result = PCD_result(next);
        let out = super::next_pair_forest_lane_v1(&lane, &result);
        assert!(out != Err(ProgramError::Custom(0x41532003)));
    }

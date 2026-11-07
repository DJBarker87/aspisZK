    fn PCD_checked_reference(old: u64, next: u64) -> bool {
        match old.checked_add(1) { Some(n) => n == next, None => false }
    }
    #[kani::ensures(|out| *out == !PCD_checked_reference(lane.tree.next_leaf_index,result.verified_afterstate.next_pair_index))]
    #[kani::modifies()]
    fn PCD_guard_segment(lane: &PoolV1PairForestLaneStateV1,
        result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
    ) -> bool {
        let afterstate = result.verified_afterstate;
        lane.tree.next_leaf_index.checked_add(1) != Some(afterstate.next_pair_index)
    }
    #[kani::proof_for_contract(PCD_guard_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_guard_contract() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());
        let _=PCD_guard_segment(&lane,&result);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_guard_control() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());
        let out=PCD_guard_segment(&lane,&result);
        assert!(out == PCD_checked_reference(lane.tree.next_leaf_index,result.verified_afterstate.next_pair_index));
    }

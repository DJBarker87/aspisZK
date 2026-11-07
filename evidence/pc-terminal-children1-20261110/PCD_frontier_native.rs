    fn PCD_frontier_reference(next: u64, level: u32, node: [u32;8], empty: [u32;8]) -> bool {
        if level >= 20 { return false; }
        if (next >> level) & 1 != 0 { return true; }
        node == empty
    }
    #[kani::requires(level < 20)]
    #[kani::ensures(|out| {
        let node = &result.verified_afterstate.next_frontier[level];
        let empty = &POOL_V1_PAIR_EMPTY_ROOTS[level];
        let words = [node[0].0,node[1].0,node[2].0,node[3].0,node[4].0,node[5].0,node[6].0,node[7].0];
        let roots = [empty[0].0,empty[1].0,empty[2].0,empty[3].0,empty[4].0,empty[5].0,empty[6].0,empty[7].0];
        let pass = PCD_frontier_reference(result.verified_afterstate.next_pair_index, level as u32, words, roots);
        *out == if pass {Ok(())} else {Err(ProgramError::Custom(0x41532003))}
    })]
    #[kani::modifies()]
    fn PCD_frontier_segment(
        result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        level: usize,
    ) -> ProgramResult {
        let afterstate = result.verified_afterstate;
        let mut cursor = afterstate.next_frontier.iter().enumerate();
        if level != 0 { let _ = cursor.nth(level - 1); }
        let Some((native_level, node)) = cursor.next() else { panic!("PCD valid iterator cut"); };
        assert!(native_level == level);
        assert!(core::ptr::eq(node, &afterstate.next_frontier[level]));
        let level = native_level;
SOURCE_SPAN
        Ok(())
    }
    #[kani::proof_for_contract(PCD_frontier_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_frontier_contract() {
        let level: usize = kani::any(); kani::assume(level < 20);
        let result = PCD_result(kani::any());
        let _ = PCD_frontier_segment(&result,level);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_frontier_control() {
        let level: usize = kani::any(); kani::assume(level < 20);
        let result = PCD_result(kani::any());
        let out = PCD_frontier_segment(&result,level);
        let node = &result.verified_afterstate.next_frontier[level];
        let empty = &POOL_V1_PAIR_EMPTY_ROOTS[level];
        let pass = (result.verified_afterstate.next_pair_index >> level)&1 != 0 || *node == *empty;
        assert!(out != if pass {Ok(())} else {Err(ProgramError::Custom(0x41532003))});
    }

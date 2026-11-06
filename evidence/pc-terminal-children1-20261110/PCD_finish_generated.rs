    fn PCD_observe(lane: &PoolV1PairForestLaneStateV1, tag: u8, key_byte: usize, level: usize, word: usize) -> u64 {
        match tag {
            0 => lane.master[key_byte] as u64,
            1 => lane.bump as u64,
            2 => lane.lane_id as u64,
            3 => lane.tree.next_leaf_index,
            4 => lane.tree.root[word].0 as u64,
            _ => lane.tree.frontier[level][word].0 as u64,
        }
    }
    fn PCD_expected_observation(lane: &PoolV1PairForestLaneStateV1, result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1, tag: u8, key_byte: usize, level: usize, word: usize) -> u64 {
        match tag {
            0 => lane.master[key_byte] as u64,
            1 => lane.bump as u64,
            2 => lane.lane_id as u64,
            3 => result.verified_afterstate.next_pair_index,
            4 => result.verified_afterstate.next_root[word].0 as u64,
            _ => result.verified_afterstate.next_frontier[level][word].0 as u64,
        }
    }
    #[kani::requires(tag < 6 && key_byte < 32 && level < 20 && word < 8)]
    #[kani::ensures(|out| match out {
        Ok(value) => PCD_observe(value, tag, key_byte, level, word) ==
          PCD_expected_observation(lane,result,tag,key_byte,level,word),
        Err(_) => false,
    })]
    #[kani::modifies()]
    fn PCD_finish_segment(lane: &PoolV1PairForestLaneStateV1,
        result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        tag: u8, key_byte: usize, level: usize, word: usize,
    ) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
        let afterstate = result.verified_afterstate;
    Ok(PoolV1PairForestLaneStateV1 {
        master: lane.master,
        bump: lane.bump,
        lane_id: lane.lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: afterstate.next_pair_index,
            root: afterstate.next_root,
            frontier: afterstate.next_frontier,
        },
    })
    }
    #[kani::proof_for_contract(PCD_finish_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_finish_contract() {
        let lane = PCD_lane(kani::any()); let result = PCD_result(kani::any());
        let tag: u8 = kani::any(); let key_byte:usize=kani::any();
        let level:usize=kani::any(); let word:usize=kani::any();
        kani::assume(tag<6 && key_byte<32 && level<20 && word<8);
        let _ = PCD_finish_segment(&lane,&result,tag,key_byte,level,word);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_finish_control() {
        let lane = PCD_lane(kani::any()); let result = PCD_result(kani::any());
        let tag: u8 = kani::any(); let key_byte:usize=kani::any();
        let level:usize=kani::any(); let word:usize=kani::any();
        kani::assume(tag<6 && key_byte<32 && level<20 && word<8);
        let out = PCD_finish_segment(&lane,&result,tag,key_byte,level,word);
        let exact = match out { Ok(value) =>
            PCD_observe(&value,tag,key_byte,level,word) == PCD_expected_observation(&lane,&result,tag,key_byte,level,word),
            Err(_) => false };
        assert!(!exact);
    }

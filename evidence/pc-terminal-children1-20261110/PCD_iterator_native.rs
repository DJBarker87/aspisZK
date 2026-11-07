    #[kani::requires(level <= 20)]
    #[kani::ensures(|out| *out == (level < 20))]
    #[kani::modifies()]
    fn PCD_iterator_segment(
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        level:usize,
    )->bool {
        let afterstate = result.verified_afterstate;
        let mut cursor = afterstate.next_frontier.iter().enumerate();
        if level != 0 { let _ = cursor.nth(level - 1); }
        match cursor.next() {
            Some((native_level,node)) => {
                assert!(native_level==level);
                assert!(level<20);
                assert!(core::ptr::eq(node,&afterstate.next_frontier[level]));
                true
            },
            None => { assert!(level==20); false }
        }
    }
    #[kani::proof_for_contract(PCD_iterator_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_iterator_contract() {
        let result=PCD_result(kani::any());let level:usize=kani::any();kani::assume(level<=20);
        let _=PCD_iterator_segment(&result,level);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_iterator_control() {
        let result=PCD_result(kani::any());let level:usize=kani::any();kani::assume(level<=20);
        let out=PCD_iterator_segment(&result,level);assert!(out!=(level<20));
    }

    #[derive(Default)]
    struct PCD_FidelityLog {
        called: bool,
        lane_ptr: usize,
        result_ptr: usize,
        reply_ok: bool,
        reply_index_or_error: u64,
    }
    fn PCD_fid_record(lane:&PoolV1PairForestLaneStateV1,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        out:&Result<PoolV1PairForestLaneStateV1,ProgramError>, log:&mut PCD_FidelityLog) {
        log.called=true;log.lane_ptr=lane as *const _ as usize;log.result_ptr=result as *const _ as usize;
        match out { Ok(value)=>{ log.reply_ok=true; log.reply_index_or_error=value.tree.next_leaf_index; },
            Err(ProgramError::Custom(code))=>{log.reply_ok=false;log.reply_index_or_error=*code as u64;},
            Err(_)=>{log.reply_ok=false;log.reply_index_or_error=u64::MAX;} }
    }
    fn PCD_fid_body(lane:&PoolV1PairForestLaneStateV1,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        reject:bool,log:&mut PCD_FidelityLog)->Result<PoolV1PairForestLaneStateV1,ProgramError> {
        let after=result.verified_afterstate;
        let out=if reject {Err(ProgramError::Custom(0x41532003))} else {Ok(PoolV1PairForestLaneStateV1 {
            master:lane.master,bump:lane.bump,lane_id:lane.lane_id,
            tree:IncrementalMerkleTreeV1 {next_leaf_index:after.next_pair_index,root:after.next_root,frontier:after.next_frontier}
        })};
        PCD_fid_record(lane,result,&out,log);out
    }
    #[kani::requires(!log.called)]
    #[kani::ensures(|_|true)]
    #[kani::modifies(log)]
    fn PCD_fid_weak(lane:&PoolV1PairForestLaneStateV1,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        reject:bool,log:&mut PCD_FidelityLog)->Result<PoolV1PairForestLaneStateV1,ProgramError> {
        PCD_fid_body(lane,result,reject,log)
    }
    #[kani::requires(!log.called)]
    #[kani::ensures(|_|false)]
    #[kani::modifies(log)]
    fn PCD_fid_inverse(lane:&PoolV1PairForestLaneStateV1,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        reject:bool,log:&mut PCD_FidelityLog)->Result<PoolV1PairForestLaneStateV1,ProgramError> {
        PCD_fid_body(lane,result,reject,log)
    }
    #[kani::requires(!log.called)]
    #[kani::ensures(|_|true)]
    #[kani::modifies(log)]
    fn PCD_fid_bad_modifies(lane:&PoolV1PairForestLaneStateV1,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        reject:bool,log:&mut PCD_FidelityLog,counter:&mut u64)->Result<PoolV1PairForestLaneStateV1,ProgramError> {
        *counter=counter.wrapping_add(1);
        PCD_fid_body(lane,result,reject,log)
    }
    fn PCD_fid_oracle(lane:&PoolV1PairForestLaneStateV1,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
        _reject:bool,log:&mut PCD_FidelityLog)->Result<PoolV1PairForestLaneStateV1,ProgramError> {
        // All actual callee Err values are Custom; arbitrary payload and arm are unconstrained.
        let out=if kani::any() {Ok(PCD_lane(kani::any()))} else {Err(ProgramError::Custom(kani::any()))};
        PCD_fid_record(lane,result,&out,log);out
    }
    fn PCD_fid_exact(out:&Result<PoolV1PairForestLaneStateV1,ProgramError>,
        result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,reject:bool)->bool {
        match out { Ok(lane)=>!reject && lane.tree.next_leaf_index==result.verified_afterstate.next_pair_index,
            Err(e)=>reject && *e==ProgramError::Custom(0x41532003) }
    }
    #[kani::proof_for_contract(PCD_fid_weak)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_fidelity_weak_contract() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());let mut log=PCD_FidelityLog::default();
        let _=PCD_fid_weak(&lane,&result,kani::any(),&mut log);
    }
    #[kani::proof_for_contract(PCD_fid_inverse)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_fidelity_inverse_contract() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());let mut log=PCD_FidelityLog::default();
        let _=PCD_fid_inverse(&lane,&result,kani::any(),&mut log);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_fidelity_real_caller() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());let reject:bool=kani::any();let mut log=PCD_FidelityLog::default();
        let out=PCD_fid_weak(&lane,&result,reject,&mut log);
        assert!(log.called&&log.lane_ptr==&lane as *const _ as usize&&log.result_ptr==&result as *const _ as usize);
        assert!(PCD_fid_exact(&out,&result,reject));
    }
    #[kani::proof]
    #[kani::stub(PCD_fid_weak,PCD_fid_oracle)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_fidelity_unimplied_caller() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());let reject:bool=kani::any();let mut log=PCD_FidelityLog::default();
        let out=PCD_fid_weak(&lane,&result,reject,&mut log);
        assert!(log.called&&log.lane_ptr==&lane as *const _ as usize&&log.result_ptr==&result as *const _ as usize);
        assert!(PCD_fid_exact(&out,&result,reject));
    }
    #[kani::proof_for_contract(PCD_fid_bad_modifies)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_fidelity_modifies_violation() {
        let lane=PCD_lane(kani::any());let result=PCD_result(kani::any());let reject:bool=kani::any();let mut log=PCD_FidelityLog::default();
        let mut counter:u64=kani::any();let before=counter;
        let _=PCD_fid_bad_modifies(&lane,&result,reject,&mut log,&mut counter);
        kani::cover!(counter!=before);
    }

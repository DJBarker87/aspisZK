    fn PCD_result_box_body(reply:&Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,log:&mut PCD_BoxLog)->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> {
        log.called=true;log.argument=reply as *const _ as usize;
        match *reply {
            Err(_)=>Err(ProgramError::InvalidInstructionData),
            Ok(value)=>{let out=Box::new(value);log.allocation=out.as_ref() as *const _ as usize;Ok(out)},
        }
    }
    #[kani::ensures(|_|true)]
    #[kani::modifies(log)]
    fn PCD_result_box_weak(reply:&Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,log:&mut PCD_BoxLog)->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> {PCD_result_box_body(reply,log)}
    #[kani::ensures(|_|false)]
    #[kani::modifies(log)]
    fn PCD_result_box_inverse(reply:&Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,log:&mut PCD_BoxLog)->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> {PCD_result_box_body(reply,log)}
    fn PCD_result_box_oracle(reply:&Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,log:&mut PCD_BoxLog)->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> {
        log.called=true;log.argument=reply as *const _ as usize;
        if kani::any() {let out=Box::new(PCD_request_value());log.allocation=out.as_ref() as *const _ as usize;Ok(out)} else {Err(ProgramError::InvalidInstructionData)}
    }
    fn PCD_result_box_exact(reply:&Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,out:&Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError>)->bool {
        match (reply,out) {(Err(_),Err(ProgramError::InvalidInstructionData))=>true,(Ok(expected),Ok(actual))=>expected.verifier_profile[0]==actual.verifier_profile[0],_=>false}
    }
    #[kani::ensures(|_|true)]
    #[kani::modifies(log)]
    fn PCD_result_box_bad_modifies(reply:&Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,log:&mut PCD_BoxLog,counter:&mut u64)->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> {
        *counter=counter.wrapping_add(1);PCD_result_box_body(reply,log)
    }
    #[kani::proof_for_contract(PCD_result_box_weak)]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_result_box_weak_contract() {let reply=PCD_decoded_request();let mut log=PCD_BoxLog::default();let _=PCD_result_box_weak(&reply,&mut log);}
    #[kani::proof_for_contract(PCD_result_box_inverse)]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_result_box_inverse_contract() {let reply=PCD_decoded_request();let mut log=PCD_BoxLog::default();let _=PCD_result_box_inverse(&reply,&mut log);}
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_result_box_real_caller() {
        let reply=PCD_decoded_request();let mut log=PCD_BoxLog::default();let out=PCD_result_box_body(&reply,&mut log);
        assert!(log.called && log.argument==&reply as *const _ as usize);assert!(PCD_result_box_exact(&reply,&out));
    }
    #[kani::proof]
    #[kani::stub(PCD_result_box_body,PCD_result_box_oracle)]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_result_box_unimplied_caller() {
        let reply=PCD_decoded_request();let mut log=PCD_BoxLog::default();let out=PCD_result_box_body(&reply,&mut log);
        assert!(log.called && log.argument==&reply as *const _ as usize);assert!(PCD_result_box_exact(&reply,&out));
    }
    #[kani::proof_for_contract(PCD_result_box_bad_modifies)]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_result_box_modifies_control() {
        let reply=PCD_decoded_request();let mut log=PCD_BoxLog::default();let mut counter:u64=kani::any();let before=counter;
        let _=PCD_result_box_bad_modifies(&reply,&mut log,&mut counter);kani::cover!(counter!=before);
    }

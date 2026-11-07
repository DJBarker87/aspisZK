    #[derive(Default)]
    struct PCD_BoxLog { called:bool, argument:usize, allocation:usize }
    fn PCD_request_value()->PoolV1PairForestTerminalRequestV1 {
        use aspis_statement::pool_v1::{PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1};
        PoolV1PairForestTerminalRequestV1 {
            verifier_profile:kani::any(),verifier_release:kani::any(),pool_program:kani::any(),
            public:if kani::any() {PoolV1PairForestTerminalPaymentV1::PrivateTransfer(PoolV1PrivateTransferPublicV1 {
                pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),
                anchor_root:PCD_digest(),nullifier:PCD_digest(),asset_id:aspis_core::field::M31(kani::any()),
                recipient_commitment:PCD_digest(),change_commitment:PCD_digest(),
            })}else{PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),
                anchor_root:PCD_digest(),nullifier:PCD_digest(),asset_id:aspis_core::field::M31(kani::any()),
                amount:kani::any(),destination_token_account:kani::any(),change_commitment:PCD_digest(),
            })},
        }
    }
    fn PCD_box_body(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog)->Box<PoolV1PairForestTerminalRequestV1> {
        let allocated=Box::new(*value);
        log.called=true;log.argument=value as *const _ as usize;
        log.allocation=allocated.as_ref() as *const _ as usize;
        allocated
    }
    #[kani::requires(tag<14&&i<8&&j<32&&offset<core::mem::size_of::<PoolV1PairForestTerminalRequestV1>())]
    #[kani::ensures(|out| PCD_request_observe(out,tag,i,j)==PCD_request_observe(value,tag,i,j))]
    #[kani::modifies(log)]
    fn PCD_box_segment(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog,tag:u8,i:usize,j:usize,offset:usize)->Box<PoolV1PairForestTerminalRequestV1> {
        PCD_box_body(value,log)
    }
    #[kani::proof_for_contract(PCD_box_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_contract() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        let tag:u8=13;
        let i:u8=kani::any();let j:u8=kani::any();kani::assume(i<8&&j<32);
        let _=PCD_box_segment(&value,&mut log,tag,i as usize,j as usize,0);
    }

    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_corrupt_control() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        let mut out=PCD_box_body(&value,&mut log);
        out.verifier_profile[0]=out.verifier_profile[0].wrapping_add(1);
        assert!(out.verifier_profile[0]==value.verifier_profile[0]);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_allocation_control() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        let original=PCD_box_body(&value,&mut log);
        let different=Box::new(value);
        assert!(different.as_ref() as *const _ as usize==log.allocation);
        drop(original);
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_fresh_control() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        let out=PCD_box_body(&value,&mut log);
        let offset:usize=kani::any();kani::assume(offset<core::mem::size_of::<PoolV1PairForestTerminalRequestV1>());
        assert!(out.as_ref() as *const _ as *const u8==( &value as *const _ as *const u8).wrapping_add(offset));
    }
    #[kani::ensures(|_|true)]
    #[kani::modifies(log)]
    fn PCD_box_weak(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog)->Box<PoolV1PairForestTerminalRequestV1> { PCD_box_body(value,log) }
    #[kani::ensures(|_|false)]
    #[kani::modifies(log)]
    fn PCD_box_inverse(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog)->Box<PoolV1PairForestTerminalRequestV1> { PCD_box_body(value,log) }
    fn PCD_box_oracle(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog)->Box<PoolV1PairForestTerminalRequestV1> {
        let out=Box::new(PCD_request_value());log.called=true;log.argument=value as *const _ as usize;
        log.allocation=out.as_ref() as *const _ as usize;out
    }
    #[kani::ensures(|_|true)]
    #[kani::modifies(log)]
    fn PCD_box_bad_modifies(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog,counter:&mut u64)->Box<PoolV1PairForestTerminalRequestV1> {
        *counter=counter.wrapping_add(1);PCD_box_body(value,log)
    }
    #[kani::proof_for_contract(PCD_box_weak)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_weak_contract() {let value=PCD_request_value();let mut log=PCD_BoxLog::default();let _=PCD_box_weak(&value,&mut log);}
    #[kani::proof_for_contract(PCD_box_inverse)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_inverse_contract() {let value=PCD_request_value();let mut log=PCD_BoxLog::default();let _=PCD_box_inverse(&value,&mut log);}
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_real_caller() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();let out=PCD_box_body(&value,&mut log);
        assert!(log.called && log.argument==&value as *const _ as usize);
        assert!(out.verifier_profile[0]==value.verifier_profile[0]);
    }
    #[kani::proof]
    #[kani::stub(PCD_box_body,PCD_box_oracle)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_unimplied_caller() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();let out=PCD_box_body(&value,&mut log);
        assert!(log.called && log.argument==&value as *const _ as usize);
        assert!(out.verifier_profile[0]==value.verifier_profile[0]);
    }
    #[kani::proof_for_contract(PCD_box_bad_modifies)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_modifies_control() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();let mut counter:u64=kani::any();let before=counter;
        let _=PCD_box_bad_modifies(&value,&mut log,&mut counter);kani::cover!(counter!=before);
    }

    #[kani::requires(offset<core::mem::size_of::<PoolV1PairForestTerminalRequestV1>())]
    #[kani::ensures(|out| log.called && log.argument==value as *const _ as usize
        && out.as_ref() as *const _ as usize==log.allocation
        && out.as_ref() as *const _ as *const u8!=(value as *const _ as *const u8).wrapping_add(offset))]
    #[kani::modifies(log)]
    fn PCD_box_owner_segment(value:&PoolV1PairForestTerminalRequestV1,log:&mut PCD_BoxLog,offset:usize)->Box<PoolV1PairForestTerminalRequestV1> { PCD_box_body(value,log) }
    #[kani::proof_for_contract(PCD_box_owner_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_owner_contract() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();let offset:usize=kani::any();
        kani::assume(offset<core::mem::size_of::<PoolV1PairForestTerminalRequestV1>());
        let _=PCD_box_owner_segment(&value,&mut log,offset);
    }

    // PCD VALUE CASE CONTROL
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_value_control() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        let tag:u8=13;
        let i:u8=kani::any();let j:u8=kani::any();kani::assume(i<8&&j<32);
        let out=PCD_box_body(&value,&mut log);
        assert!(PCD_request_observe(&out,tag,i as usize,j as usize)!=PCD_request_observe(&value,tag,i as usize,j as usize));
    }

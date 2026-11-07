    fn PCD_request_observe(value:&PoolV1PairForestTerminalRequestV1,tag:u8,i:usize,j:usize)->u64 {
        if tag==0 { return value.verifier_profile[j] as u64; }
        if tag==1 { return value.verifier_release[j] as u64; }
        if tag==2 { return value.pool_program[j] as u64; }
        match value.public {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>match tag {
                3=>1,4=>p.pool[j] as u64,5=>p.deployment_domain[j] as u64,
                6=>p.anchor_sequence,7=>p.anchor_root[i].0 as u64,
                8=>p.nullifier[i].0 as u64,9=>p.asset_id.0 as u64,
                10=>p.change_commitment[i].0 as u64,11=>p.recipient_commitment[i].0 as u64,_=>0,
            },
            PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>match tag {
                3=>2,4=>p.pool[j] as u64,5=>p.deployment_domain[j] as u64,
                6=>p.anchor_sequence,7=>p.anchor_root[i].0 as u64,
                8=>p.nullifier[i].0 as u64,9=>p.asset_id.0 as u64,
                10=>p.change_commitment[i].0 as u64,12=>p.amount as u64,
                13=>p.destination_token_account[j] as u64,_=>0,
            },
        }
    }
    pub(super) fn PCD_request_exact(out:&Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError>,bytes:&[u8],tag:u8,i:usize,j:usize)->bool {
        match request_ref(bytes) {
            Err(error)=>match out {Err(actual)=>*actual==error,Ok(_)=>false},
            Ok(expected)=>match out {Err(_)=>false,Ok(actual)=>PCD_request_observe(actual,tag,i,j)==PCD_request_observe(&expected,tag,i,j)},
        }
    }
    #[kani::proof_for_contract(super::decode_terminal_request_box_v1)]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_request_contract() {
        let bytes = PCD_request_bytes();
        let out=super::decode_terminal_request_box_v1(&bytes);
        kani::cover!(out.is_ok());kani::cover!(out.is_err());
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]
    fn PCD_request_control() {
        let bytes = PCD_request_bytes();let out=super::decode_terminal_request_box_v1(&bytes);
        kani::assume(out.is_ok());
        let tag:u8=kani::any();let i:usize=kani::any();let j:usize=kani::any();
        kani::assume(tag<14&&i<8&&j<32);
        assert!(!PCD_request_exact(&out,&bytes,tag,i,j));
    }
    fn PCD_request_bytes()->[u8;320] { [kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any()] }

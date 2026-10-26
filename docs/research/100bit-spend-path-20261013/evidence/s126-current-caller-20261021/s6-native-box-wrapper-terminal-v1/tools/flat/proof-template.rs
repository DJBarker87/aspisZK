#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
    use aspis_statement::pool_v1::pair_forest_terminal::{
        PoolV1PairForestTerminalStatementV1 as Statement,
        PoolV1PairForestTerminalStatementV1,
        PoolV1PairForestTerminalFormatErrorV1 as FormatError,
        decode_pool_v1_pair_forest_terminal_statement_v1,
    };
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    // The frozen solana_program::program_error module re-exports this exact
    // SDK type. Its release version/checksum and re-export are separately pinned.
    use solana_program_error::ProgramError;

// GENERATED_NATIVE_WRAPPER

    // GENERATED_CONSTRUCTORS
    // GENERATED_OBSERVER

    static mut ANSWER:Option<Result<Statement,FormatError>>=None;
    static mut CALLS:u8=0;
    static mut SEEN:*const u8=core::ptr::null();
    static mut LENGTH:usize=0;
    fn decoder_return(bytes:&[u8])->Result<Statement,FormatError> {
        unsafe {
            CALLS+=1;
            assert!(CALLS==1);
            SEEN=bytes.as_ptr();LENGTH=bytes.len();
            ANSWER.take().expect("one native decoder reply")
        }
    }

    fn aliases(statement:&Statement, selected:Public<'_>)->bool {
        match (statement,selected) {
            (Statement::PrivateTransfer{common,public},Public::Transfer(p,lane))=>
                core::ptr::eq(p,public)&&core::ptr::eq(lane,&common.lane_transition),
            (Statement::Withdrawal{common,public},Public::Withdrawal(p,lane))=>
                core::ptr::eq(p,public)&&core::ptr::eq(lane,&common.lane_transition),
            _=>false,
        }
    }

    fn run(negative:bool) {
    // GENERATED_BYTES
        let index:usize=kani::any();
        let answer=if kani::any::<bool>() {Ok(arbitrary_statement())} else {Err(kani::any::<FormatError>())};
        unsafe {ANSWER=Some(answer);CALLS=0;SEEN=core::ptr::null();LENGTH=0;}
        let returned=decode_public_statement_box(&bytes);
        unsafe {
            assert!(CALLS==1);
            assert!(SEEN==bytes.as_ptr());
            assert!(LENGTH==bytes.len());
            assert!(ANSWER.is_none());
        }
        match (answer,returned) {
            (Ok(mut before),Ok(after))=> {
                if negative {
                    // Only the final common frontier coordinate is changed.
                    match &mut before {
                        Statement::PrivateTransfer{common,..}|Statement::Withdrawal{common,..}=>
                            common.lane_transition.candidate_afterstate.next_frontier[19][7].0^=1,
                    }
                }
                assert!(observe(&before,index)==observe(&after,index));
                assert!(aliases(&after,after.semantic_public()));
                match &*after {
                    Statement::PrivateTransfer{..}=>kani::cover!(true,"transfer boxed return"),
                    Statement::Withdrawal{..}=>kani::cover!(true,"withdrawal boxed return"),
                }
                // Actual native Box destructor is executed after its last use.
                drop(after);
            },
            (Err(_),Err(error))=> {
                assert!(matches!(error,ProgramError::InvalidAccountData));
                kani::cover!(true,"native decoder error mapped");
            },
            _=>assert!(false,"native wrapper result classification differs"),
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_projection() {run(false);}

    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn last_frontier_negative_control() {run(true);}
}

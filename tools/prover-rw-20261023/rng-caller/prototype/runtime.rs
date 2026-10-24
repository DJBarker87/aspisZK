use prover_rw_rng_caller::*;

fn policy() -> impl FnMut(usize)->[u8;32] {
        let mut calls=0u8;
        move |k| {calls+=1; let mut n=[calls;32]; n[31]=k as u8; n}
    }
    fn tape(blocks:Vec<([u8;64],Result<(),getrandom::Error>)>)->Tape {Tape{replies:blocks,used:0}}
    #[test]
    fn changing_draws_rejected_body_then_success() {
        let body=|s:StateOnlyAttemptSecrets,mut ledger:Vec<[u8;32]>| {
            ledger.push(s.mask_nonce);
            let r=if ledger.len()==1 {Err(Error::Rejected)} else {Ok((vec![42],9))};
            (ledger,r)
        };
        let (p,mut n,ledger,_,r)=prove_masked_retrying_with(true,
            tape(vec![([0;64],Ok(())),([1;64],Ok(())),([2;64],Ok(()))]),policy(),vec![],body);
        assert_eq!(p.used,3); assert_eq!(ledger.len(),2);
        assert_eq!(ledger[0][0],1); assert_eq!(ledger[1][0],2);
        let r=r.unwrap();assert_eq!(r.attempts,2);assert_eq!(r.proof,vec![42]);
        assert_eq!(n(2)[0],3);
    }
    #[test]
    fn native_error_and_policy_state_survive() {
        let error=getrandom::Error::new_custom(1234);
        match StateOnlyAttemptEntropyError::from(error) {
            StateOnlyAttemptEntropyError::Os(e)=>assert_eq!(e,error), _=>panic!(),
        }
        let body=|_:StateOnlyAttemptSecrets,l:Vec<[u8;32]>| (l,Err(Error::Rejected));
        let (p,mut n,l,_,r)=prove_masked_retrying_with(true,tape(vec![([7;64],Err(error))]),policy(),vec![],body);
        assert_eq!(p.used,1);assert!(l.is_empty());assert!(matches!(r,Err(Error::Entropy)));
        assert_eq!(n(1)[0],2);
    }
    #[test]
    fn duplicate_is_fatal_and_preserves_advanced_state() {
        let body=|s:StateOnlyAttemptSecrets,mut ledger:Vec<[u8;32]>| {
            let r=if ledger.contains(&s.mask_nonce) {Err(Error::Semantic)}
            else {ledger.push(s.mask_nonce);Err(Error::Rejected)};
            (ledger,r)
        };
        let n=|_|[1;32];
        let (p,_,l,_,r)=prove_masked_retrying_with(true,
            tape(vec![([1;64],Ok(())),([2;64],Ok(())),([3;64],Ok(()))]),n,vec![],body);
        assert_eq!(p.used,2);assert_eq!(l.len(),1);assert!(matches!(r,Err(Error::Semantic)));
    }
    #[test]
    fn cap8_and_variant_guards_preserve_policy() {
        let body=|_:StateOnlyAttemptSecrets,l:usize| (l+1,Err(Error::Rejected));
        let (p,mut n,l,_,r)=prove_masked_retrying_with(true,
            tape(vec![([1;64],Ok(()));8]),policy(),0,body);
        assert_eq!(p.used,8);assert_eq!(l,8);assert!(matches!(r,Err(Error::AttemptsExhausted)));
        assert_eq!(n(8)[0],9);
        let (p,mut n,l,_,r)=prove_masked_retrying_with(false,tape(vec![]),policy(),0,body);
        assert_eq!(p.used,0);assert_eq!(l,0);assert!(matches!(r,Err(Error::Semantic)));
        assert_eq!(n(0)[0],1);
    }

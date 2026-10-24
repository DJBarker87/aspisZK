//! Actual factory snapshot with verified loop invariant; real Drop retained.
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![allow(non_snake_case)]
mod ProverRwFactoryIterationFrame {
    include!("selected.rs");
    #[cfg(kani)]
    mod checks {
        use super::*;
        pub(super) static mut CALLS: usize = 0;
        pub(super) static mut LAST: [u8;64] = [0;64];
        pub(super) static mut LAST_ERROR: Option<getrandom::Error> = None;
        pub(super) static mut PRIOR_REJECTED: bool = true;
        pub(super) static mut PROVIDER_STATE: u64 = 0;
        pub(super) static mut LAST_STATE: u64 = 0;
        fn half_nonzero(bytes: &[u8]) -> bool {
            let mut any=false;
            for i in 0..bytes.len() { any |= bytes[i] != 0; }
            any
        }
        // The ONLY stub. No source branch or destructor is replaced.
        fn fill_stub(dest: &mut [u8]) -> Result<(),getrandom::Error> {
            assert_eq!(dest.len(),64);
            unsafe {
                assert!(CALLS < 16);
                assert!(PRIOR_REJECTED);
            }
            for i in 0..64 { assert_eq!(dest[i],0); }
            let post=kani::any::<[u8;64]>();
            let failed=kani::any::<bool>();
            // Safe public constructor: arbitrary custom code. OS code identity
            // generalization remains source-inspected, not quantified here.
            let error=getrandom::Error::new_custom(kani::any());
            let state=kani::any::<u64>();
            dest.copy_from_slice(&post);
            unsafe {
                CALLS+=1;
                LAST=post;
                LAST_ERROR=if failed {Some(error)} else {None};
                PRIOR_REJECTED=!failed && !(half_nonzero(&post[..32]) && half_nonzero(&post[32..]));
                PROVIDER_STATE=state;
                LAST_STATE=state;
            }
            if failed {Err(error)} else {Ok(())}
        }
        #[kani::proof]
        #[kani::unwind(66)]
        #[kani::stub(getrandom::fill, fill_stub)]
        fn all_outcomes() {
            let nonce=kani::any::<[u8;32]>();
            let initial_state=kani::any::<u64>();
            unsafe { PROVIDER_STATE=initial_state; }
            let result=StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce);
            unsafe {
                let calls=CALLS;
                assert!(calls<=16);
                if nonce==[0;32] {
                    assert_eq!(calls,0);
                    assert_eq!(PROVIDER_STATE,initial_state);
                    assert!(matches!(result,Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
                } else {
                    assert!(calls>=1);
                    assert_eq!(PROVIDER_STATE,LAST_STATE);
                    let last=LAST;
                    let last_error=LAST_ERROR;
                    match result {
                        Ok(owner) => {
                            assert!(last_error.is_none());
                            assert_eq!(owner.mask_nonce,nonce);
                            assert!(half_nonzero(&last[..32]) && half_nonzero(&last[32..]));
                            let i=(kani::any::<u8>() % 32) as usize;
                            assert_eq!(owner.field_mask_entropy[i],last[i]);
                            assert_eq!(owner.leaf_salt_seed[i],last[i+32]);
                            // Actual owner drop glue executes at this scope end.
                        }
                        Err(StateOnlyAttemptEntropyError::Os(error)) => {
                            assert_eq!(last_error,Some(error));
                        }
                        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock) => {
                            assert_eq!(calls,16);
                            assert!(last_error.is_none());
                            assert!(PRIOR_REJECTED);
                        }
                    }
                }
            }
        }
    }
}

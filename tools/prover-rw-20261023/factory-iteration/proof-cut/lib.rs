//! Concrete one-draw cut. No whole-factory execution or event-transport claim.
#![allow(non_snake_case)]
mod ProverRwFactoryIterationCut {
    include!("selected.rs");
    #[cfg(kani)]
    mod checks {
        use super::*;
        static mut CALLS: usize=0;
        static mut LAST: [u8;64]=[0;64];
        static mut LAST_ERROR: Option<getrandom::Error>=None;
        static mut PROVIDER_STATE: u64=0;
        static mut LAST_STATE: u64=0;
        fn half_nonzero(bytes: &[u8])->bool {
            let mut any=false;
            for i in 0..bytes.len() {any|=bytes[i]!=0;}
            any
        }
        // Sole OS-boundary abstraction: arbitrary postbuffer and custom error.
        fn fill_stub(dest: &mut [u8])->Result<(),getrandom::Error> {
            assert_eq!(dest.len(),64);
            unsafe {assert_eq!(CALLS,0);}
            for i in 0..64 {assert_eq!(dest[i],0);}
            let post=kani::any::<[u8;64]>();
            let failed=kani::any::<bool>();
            let error=getrandom::Error::new_custom(kani::any());
            let state=kani::any::<u64>();
            dest.copy_from_slice(&post);
            unsafe {
                CALLS=1; LAST=post;
                LAST_ERROR=if failed {Some(error)} else {None};
                PROVIDER_STATE=state; LAST_STATE=state;
            }
            if failed {Err(error)} else {Ok(())}
        }
        #[kani::proof]
        #[kani::unwind(66)]
        #[kani::stub(getrandom::fill,fill_stub)]
        fn one_draw_relation() {
            // Exhausts entry counts0..15 and every byte array; no result assume.
            let entry=(kani::any::<u8>() % 16) as usize;
            let nonce=kani::any::<[u8;32]>();
            unsafe {PROVIDER_STATE=kani::any::<u64>();}
            let result=StateOnlyAttemptSecrets::one_draw(nonce,entry);
            unsafe {
                let calls=CALLS;
                assert_eq!(calls,1);
                assert_eq!(PROVIDER_STATE,LAST_STATE);
                let post=LAST;
                let last_error=LAST_ERROR;
                match result {
                    Err(StateOnlyAttemptEntropyError::Os(error))=>{
                        assert_eq!(last_error,Some(error));
                    }
                    Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)=>assert!(false),
                    Ok((retry,owner))=>{
                        assert!(last_error.is_none());
                        let accepted=half_nonzero(&post[..32]) && half_nonzero(&post[32..]);
                        assert_eq!(owner.is_some(),accepted);
                        match owner {
                            Some(owner)=>{
                                assert_eq!(retry,entry);
                                assert_eq!(owner.mask_nonce,nonce);
                                // One symbolic index quantifies every returned byte.
                                let i=(kani::any::<u8>() % 32) as usize;
                                assert_eq!(owner.field_mask_entropy[i],post[i]);
                                assert_eq!(owner.leaf_salt_seed[i],post[i+32]);
                                // The actual returned owner destructor executes here.
                            }
                            None=>{
                                assert_eq!(retry,entry+1);
                                assert!(retry<=16);
                                assert_eq!(retry==16,entry==15);
                                assert_eq!(16-retry+1,16-entry);
                            }
                        }
                    }
                }
            }
        }
    }
}

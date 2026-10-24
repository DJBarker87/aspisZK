//! Prospective actual owned source. Instrumented memory-model claims only.
#![allow(non_snake_case)]
mod ProverRwResumeP6 {
    include!("selected.rs");
    #[cfg(kani)]
    mod checks {
        use super::*;
        static mut CALLS: usize=0;
        static mut LAST: [u8;64]=[0;64];
        static mut LAST_ERROR: Option<getrandom::Error>=None;
        static mut LEDGER: u64=0;
        static mut AFTER: u64=0;
        fn fill_boundary(dest: &mut [u8])->Result<(),getrandom::Error> {
            assert_eq!(dest.len(),64);
            unsafe { assert_eq!(CALLS,0); }
            for i in 0..64 { assert_eq!(dest[i],0); }
            let post=kani::any::<[u8;64]>();
            let failed=kani::any::<bool>();
            let repr=kani::any::<i32>();
            // This is exactly the valid representation domain, not an OS errno law.
            let code=core::num::NonZeroI32::new(repr);
            kani::assume(code.is_some());
            let error=getrandom::Error::prover_rw_resume_p6_from_repr(code.unwrap());
            let after=kani::any::<u64>();
            dest.copy_from_slice(&post);
            unsafe {
                CALLS=1; LAST=post; LAST_ERROR=if failed {Some(error)} else {None};
                LEDGER=after; AFTER=after;
            }
            if failed {Err(error)} else {Ok(())}
        }
        fn nonzero(bytes:&[u8])->bool {
            let mut b=0;for x in bytes {b|=*x;} b!=0
        }
        fn event(index:usize,len:usize,expected:&[u8]) {
            let (events,count)=zeroize::ProverRwResumeP6::events();
            assert!(index<count);
            let e=events[index];
            assert_eq!(e.ordinal,index);
            assert_eq!(e.before.len,len);assert_eq!(e.after.len,len);
            // Independent symbolic coordinate covers the full initialized payload.
            let i=(kani::any::<u8>() as usize)%len;
            assert_eq!(e.before.bytes[i],expected[i]);
            assert_eq!(e.after.bytes[i],0);
        }
        #[kani::proof]
        #[kani::unwind(66)]
        #[kani::stub(getrandom::fill,fill_boundary)]
        fn native_draw_resume_events() {
            let entry=(kani::any::<u8>()%16) as usize;
            let nonce=kani::any::<[u8;32]>();
            unsafe {LEDGER=kani::any();}
            let request=ProverRwResumeP6Request {mask_nonce:nonce,retry:entry};
            // Actual prospective source calls the literal fill on freshzero64.
            let draw=request.draw();
            assert_eq!(draw.request.mask_nonce,nonce);assert_eq!(draw.request.retry,entry);
            let post=unsafe {LAST};let failed=unsafe {LAST_ERROR};
            assert_eq!(draw.outcome.err(),failed);
            let i=(kani::any::<u8>()%64) as usize;
            assert_eq!(draw.bytes[i],post[i]);
            assert_eq!(zeroize::ProverRwResumeP6::events().1,0);
            let (control,result)=draw.resume();
            unsafe {let ledger=LEDGER;let after=AFTER;let calls=CALLS;
                assert_eq!(ledger,after);assert_eq!(calls,1);}
            match failed {
                Some(error)=>{
                    assert!(matches!(control,ProverRwResumeP6Control::Done));
                    match result {Err(StateOnlyAttemptEntropyError::Os(actual))=>assert_eq!(actual,error),_=>assert!(false)}
                    assert_eq!(zeroize::ProverRwResumeP6::events().1,1);
                    event(0,64,&post);
                }
                None=>{
                    let accepted=nonzero(&post[..32]) && nonzero(&post[32..]);
                    if accepted {
                        assert!(matches!(control,ProverRwResumeP6Control::Done));
                        let owner=match result {Ok(Some(owner))=>owner,_=>{assert!(false);return}};
                        assert_eq!(zeroize::ProverRwResumeP6::events().1,1);
                        event(0,64,&post);
                        assert_eq!(owner.mask_nonce,nonce);
                        let i=(kani::any::<u8>()%32) as usize;
                        assert_eq!(owner.field_mask_entropy[i],post[i]);
                        assert_eq!(owner.leaf_salt_seed[i],post[i+32]);
                        // Distinct later returned-owner field-drop phase, never a stub.
                        drop(owner);
                        assert_eq!(zeroize::ProverRwResumeP6::events().1,3);
                        event(1,32,&post[..32]);event(2,32,&post[32..]);
                    } else {
                        if entry<15 {
                            match control {ProverRwResumeP6Control::More(next)=>{
                                assert_eq!(next.mask_nonce,nonce);assert_eq!(next.retry,entry+1);
                                assert_eq!(16-next.retry+1,16-entry);
                            },_=>assert!(false)}
                            assert!(matches!(result,Ok(None)));
                        } else {
                            assert!(matches!(control,ProverRwResumeP6Control::Done));
                            assert!(matches!(result,Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
                        }
                        assert_eq!(zeroize::ProverRwResumeP6::events().1,3);
                        event(0,32,&post[32..]);event(1,32,&post[..32]);event(2,64,&post);
                    }
                }
            }
        }
    }
}

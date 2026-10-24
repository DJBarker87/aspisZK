//! Prepared paired source relation. ZERO Kani invocations authorized in this step.
#![allow(non_snake_case, dead_code, unexpected_cfgs)]
#[derive(Debug, PartialEq, Eq)]
pub enum ResultProjection { Os(getrandom::Error), Exhausted, More, Owner(u8,u8,u8) }
#[derive(Debug, PartialEq, Eq)]
pub struct Projection { pub retry: Option<(usize,u8)>, pub result: ResultProjection }
pub mod Instrumented {
    include!("selected.rs");
    include!("observe.rs");
}
pub mod Original {
    use zeroize_original as zeroize;
    include!("selected.rs");
    include!("observe.rs");
}
#[cfg(kani)]
mod checks {
    use super::*;
    use zeroize::ProverRwResumeScalar as Ghost;
    static mut POST: [u8;64] = [0;64];
    static mut ERROR: Option<getrandom::Error> = None;
    static mut NEXT: u64 = 0;
    static mut LEDGER: u64 = 0;
    static mut CALLS: u8 = 0;
    fn fill_boundary(dest: &mut [u8]) -> Result<(),getrandom::Error> {
        assert_eq!(dest.len(),64);
        let j=Ghost::coordinate();
        assert_eq!(dest[j],0); assert_eq!(dest[j+32],0);
        unsafe {
            assert!(CALLS<2); CALLS+=1;
            dest.copy_from_slice(&POST);
            LEDGER=NEXT;
            match ERROR { Some(error)=>Err(error), None=>Ok(()) }
        }
    }
    fn event(e: Ghost::Event, len:usize, low:u8, high:u8) {
        assert_eq!(e.before,Ghost::Observation {len,low,high});
        assert_eq!(e.after,Ghost::Observation {len,low:0,high:0});
    }
    fn instrumented_phase(success:bool) {
        let (a,b,c,count,overflow)=Ghost::events();
        assert!(!overflow);
        let j=Ghost::coordinate();
        let (low,high,failed)=unsafe {(POST[j],POST[j+32],ERROR.is_some())};
        if failed || success {
            // For success the returned32 fields are still LIVE at this call.
            assert_eq!(count,1); event(a,64,low,high);
        } else {
            assert_eq!(count,3);
            event(a,32,high,0); event(b,32,low,0); event(c,64,low,high);
        }
    }
    fn original_phase(_:bool) {}
    fn nonzero(bytes:&[u8])->bool {
        let mut combined=0; for byte in bytes {combined|=*byte;} combined!=0
    }
    #[kani::proof]
    #[kani::unwind(66)]
    #[kani::stub(getrandom::fill,fill_boundary)]
    fn paired_coordinate_native_resume() {
        // The sole coordinate choice; covers all32 indices for all complete inputs.
        let raw_j=kani::any::<u8>();
        Ghost::initialize(raw_j);
        let j=(raw_j%32) as usize;
        let nonce=kani::any::<[u8;32]>();
        let post=kani::any::<[u8;64]>();
        let entry=(kani::any::<u8>()%16) as usize;
        let failed=kani::any::<bool>();
        let repr=kani::any::<i32>();
        let code=core::num::NonZeroI32::new(repr);
        kani::assume(code.is_some());
        let error=getrandom::Error::prover_rw_resume_scalar_from_repr(code.unwrap());
        let next=kani::any::<u64>();
        unsafe { POST=post; ERROR=if failed {Some(error)} else {None};
            NEXT=next; LEDGER=kani::any(); }
        let instrumented=Instrumented::run(nonce,entry,j,instrumented_phase);
        let accepted=!failed && nonzero(&post[..32]) && nonzero(&post[32..]);
        let expected=if failed {
            Projection {retry:None,result:ResultProjection::Os(error)}
        } else if accepted {
            Projection {retry:None,result:ResultProjection::Owner(nonce[j],post[j],post[j+32])}
        } else if entry<15 {
            Projection {retry:Some((entry+1,nonce[j])),result:ResultProjection::More}
        } else { Projection {retry:None,result:ResultProjection::Exhausted} };
        assert_eq!(instrumented,expected);
        let ghost_after=Ghost::events();
        let (a,b,c,count,overflow)=ghost_after;
        assert!(!overflow); assert_eq!(count,if failed {1} else {3});
        if accepted {
            event(a,64,post[j],post[j+32]);
            event(b,32,post[j],0); event(c,32,post[j+32],0);
        }
        unsafe { let ledger=LEDGER; let calls=CALLS; assert_eq!(ledger,next); assert_eq!(calls,1); }
        let original=Original::run(nonce,entry,j,original_phase);
        assert_eq!(original,instrumented);
        assert_eq!(Ghost::events(),ghost_after);
        unsafe { let ledger=LEDGER; let calls=CALLS; assert_eq!(ledger,next); assert_eq!(calls,2); }
    }
}

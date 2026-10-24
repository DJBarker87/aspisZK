//! Concrete one-draw sequential observation relation. Native provenance remains open.
#![allow(non_snake_case)]
#[derive(PartialEq,Eq,Debug)]
enum ObservedResult { Os(getrandom::Error), Exhausted, More, Owner((u8,u8,u8)) }
#[derive(PartialEq,Eq,Debug)]
struct Observation {retry:Option<(usize,u8)>,result:ObservedResult}
mod Instrumented {
    include!("../proof/selected.rs");
    include!("observe.rs");
}
mod Original {
    use zeroize_original as zeroize;
    include!("../proof/selected.rs");
    include!("observe.rs");
}
#[cfg(kani)]
mod checks {
    static mut POST:[u8;64]=[0;64];
    static mut ERROR:Option<getrandom::Error>=None;
    static mut NEXT:u64=0;
    static mut LEDGER:u64=0;
    static mut CALLS:usize=0;
    fn fill_boundary(dest:&mut[u8])->Result<(),getrandom::Error> {
        assert_eq!(dest.len(),64);
        for i in 0..64 {assert_eq!(dest[i],0);}
        unsafe {
            assert!(CALLS<2);CALLS+=1;
            let post=POST;dest.copy_from_slice(&post);
            LEDGER=NEXT;
            match ERROR {Some(error)=>Err(error),None=>Ok(())}
        }
    }
    #[kani::proof]
    #[kani::unwind(66)]
    #[kani::stub(getrandom::fill,fill_boundary)]
    fn paired_source_observation() {
        let nonce=kani::any::<[u8;32]>();
        let entry=(kani::any::<u8>()%16) as usize;
        let i=(kani::any::<u8>()%32) as usize;
        let failed=kani::any::<bool>();
        let repr=kani::any::<i32>();
        let code=core::num::NonZeroI32::new(repr);
        kani::assume(code.is_some());
        let error=getrandom::Error::prover_rw_resume_p6_from_repr(code.unwrap());
        let next=kani::any::<u64>();
        unsafe {
            POST=kani::any();ERROR=if failed {Some(error)} else {None};
            NEXT=next;LEDGER=kani::any();
        }
        let instrumented=super::Instrumented::run(nonce,entry,i);
        unsafe {let ledger=LEDGER;let calls=CALLS;assert_eq!(ledger,next);assert_eq!(calls,1);}
        let (_,count)=zeroize::ProverRwResumeP6::events();
        assert_eq!(count,if failed {1} else {3});
        let original=super::Original::run(nonce,entry,i);
        unsafe {let ledger=LEDGER;let calls=CALLS;assert_eq!(ledger,next);assert_eq!(calls,2);}
        assert_eq!(zeroize::ProverRwResumeP6::events().1,count);
        assert_eq!(instrumented,original);
    }
}

// Relational one-iteration checks. Unconstrained scalar transitions are
// explicit inputs shared by both runs. No scalar contract is assumed here.
#[cfg(kani)]
mod iteration17 {
    use super::*;
    use crate::prover_commit_reference::{self as reference, State};
    const ZERO:State=State{seed:[0;32],counter:0,block:[0;32],word:0};
    static mut BEFORE:State=ZERO;
    static mut AFTER:State=ZERO;
    static mut M:Result<M31,StateOnlyMaskBuildError>=Ok(M31::ZERO);
    static mut Q:Result<QM31,StateOnlyMaskBuildError>=Ok(QM31::ZERO);
    static mut CALLS:usize=0;
    fn record(state:State)->State {
        unsafe {
            assert_eq!(state,BEFORE);assert!(CALLS==0);CALLS+=1;AFTER
        }
    }
    fn m_borrowed(state:&mut SeedExpander)->Result<M31,StateOnlyMaskBuildError> {
        let after=record(State{seed:state.seed,counter:state.counter,block:state.block,word:state.word});
        state.seed=after.seed;state.counter=after.counter;state.block=after.block;state.word=after.word;
        unsafe {M}
    }
    fn m_owned(_:aspis_core::HashFn,_:&[u8],state:State)->(Result<M31,StateOnlyMaskBuildError>,State) {
        let after=record(state);unsafe {(M,after)}
    }
    fn q_borrowed(state:&mut SeedExpander)->Result<QM31,StateOnlyMaskBuildError> {
        let after=record(State{seed:state.seed,counter:state.counter,block:state.block,word:state.word});
        state.seed=after.seed;state.counter=after.counter;state.block=after.block;state.word=after.word;
        unsafe {Q}
    }
    fn q_owned(_:aspis_core::HashFn,_:&[u8],state:State)->(Result<QM31,StateOnlyMaskBuildError>,State) {
        let after=record(state);unsafe {(Q,after)}
    }
    fn setup()->State {
        let before:State=kani::any();unsafe {BEFORE=before;AFTER=kani::any();CALLS=0;}before
    }
    fn borrowed(state:State)->SeedExpander {
        SeedExpander{hash:crate::HOST_HASH,seed:state.seed,counter:state.counter,block:state.block,word:state.word}
    }
    fn retained(actual:&SeedExpander,after:State) {
        assert_eq!(actual.seed,after.seed);assert_eq!(actual.counter,after.counter);
        assert_eq!(actual.block,after.block);assert_eq!(actual.word,after.word);
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(SeedExpander::m31,m_borrowed)]
    #[kani::stub(reference::limb_caller,m_owned)]
    fn m31_push() {
        let before=setup();
        unsafe {M=if kani::any::<bool>(){Ok(M31(kani::any()))}else{Err(StateOnlyMaskBuildError::MaskSampleExhausted)};}
        let initial:M31=M31(kani::any());
        let (expected,values,after)=reference::collect_m31_owned(crate::HOST_HASH,b"scalar trace",before,1,vec![initial]);
        assert_eq!(unsafe{CALLS},1);unsafe{CALLS=0;}
        let mut actual=borrowed(before);let mut observed=vec![initial];
        let status=(|| {for _ in 0..1 {observed.push(actual.m31()?);}Ok(())})();
        assert_eq!(status,expected);assert_eq!(observed,values);retained(&actual,after);
        assert_eq!(unsafe{CALLS},1);
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(SeedExpander::qm31,q_borrowed)]
    #[kani::stub(reference::qm31_caller,q_owned)]
    fn qm31_push() {
        let before=setup();let raw:[u32;4]=kani::any();
        let value=QM31{c0:CM31::new(M31(raw[0]),M31(raw[1])),c1:CM31::new(M31(raw[2]),M31(raw[3]))};
        unsafe {Q=if kani::any::<bool>(){Ok(value)}else{Err(StateOnlyMaskBuildError::MaskSampleExhausted)};}
        let initial=QM31::ZERO;
        let (expected,values,after)=reference::collect_qm31_owned(crate::HOST_HASH,b"scalar trace",before,1,vec![initial]);
        assert_eq!(unsafe{CALLS},1);unsafe{CALLS=0;}
        let mut actual=borrowed(before);let mut observed=vec![initial];
        let status=(|| {for _ in 0..1 {observed.push(actual.qm31()?);}Ok(())})();
        assert_eq!(status,expected);assert_eq!(observed,values);retained(&actual,after);
        assert_eq!(unsafe{CALLS},1);
    }
    // Owned transition at an arbitrary padding-row predicate, using fresh
    // state on the branch. The full 1024-row caller is deliberately absent.
    fn padding_owned(state:State,old:QM31,active:bool,row:usize,dependent:usize)
        ->(Result<(),StateOnlyMaskBuildError>,QM31,State) {
        if !active && row!=dependent {
            let (sample,after)=q_owned(crate::HOST_HASH,b"scalar trace",state);
            match sample {Ok(value)=>(Ok(()),value,after),Err(e)=>(Err(e),old,after)}
        } else {(Ok(()),old,state)}
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(SeedExpander::qm31,q_borrowed)]
    fn padding_row() {
        let before=setup();let raw:[u32;4]=kani::any();
        let value=QM31{c0:CM31::new(M31(raw[0]),M31(raw[1])),c1:CM31::new(M31(raw[2]),M31(raw[3]))};
        unsafe {Q=if kani::any::<bool>(){Ok(value)}else{Err(StateOnlyMaskBuildError::MaskSampleExhausted)};}
        let row:usize=kani::any();let dependent:usize=kani::any();let active:bool=kani::any();
        let old=QM31::ONE;
        let (expected,value,after)=padding_owned(before,old,active,row,dependent);
        let count=unsafe{CALLS};unsafe{CALLS=0;}
        let mut actual=borrowed(before);let mut observed=old;
        let status=(|| {if !active && row!=dependent {observed=actual.qm31()?;}Ok(())})();
        assert_eq!(status,expected);assert_eq!(observed,value);retained(&actual,after);
        assert_eq!(unsafe{CALLS},count);assert_eq!(count,usize::from(!active && row!=dependent));
    }
}

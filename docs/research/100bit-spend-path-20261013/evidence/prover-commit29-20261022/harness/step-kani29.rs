#[cfg(kani)]
mod step_kani29 {
    use super::*;
    #[derive(Clone,Copy)]
    pub struct Oracle<'a>(&'a RefCell<OracleState>);
    pub struct OracleState {
        answers:[[u8;32];3], calls:Vec<Vec<Vec<u8>>>, next:usize, replay:bool,
    }
    impl Digest32 for Oracle<'_> {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let mut s=self.0.borrow_mut();
            let i=s.next; assert!(i<3);
            if s.replay {
                assert_eq!(s.calls[i].len(),parts.len());
                for j in 0..parts.len() {assert_eq!(s.calls[i][j].as_slice(),parts[j]);}
            } else {
                s.calls.push(parts.iter().map(|part|part.to_vec()).collect());
            }
            s.next+=1; s.answers[i]
        }
    }
    // Filled verbatim from the single native loop statement by install-kani.py.
    fn shipped_iteration<H:Digest32>(mut st:SemanticTranscript<H>, row:u8,
        record:Vec<u8>,mut sem:[K;25])->Result<(SemanticTranscript<H>,[K;25]),Error> {
        NATIVE_ITERATION
        Ok((st,sem))
    }
    // Shared arbitrary pure sampler result; check both identical call inputs.
    static mut SAMPLE_INPUT:[u8;32]=[0;32];
    static mut SAMPLE_OUTPUT:K=K::ZERO;
    static mut SAMPLE_NEXT:usize=0;
    static mut SAMPLE_REPLAY:bool=false;
    fn shared_sample(block:&[u8;32])->K {
        unsafe {
            if SAMPLE_REPLAY {assert_eq!(*block,SAMPLE_INPUT);}
            else {SAMPLE_INPUT=*block;}
            SAMPLE_NEXT+=1;
            SAMPLE_OUTPUT
        }
    }
    fn check<const N:usize>() {
        let x:[u32;4]=kani::any();
        unsafe {SAMPLE_OUTPUT=K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}};SAMPLE_REPLAY=false;SAMPLE_NEXT=0;}

        let row:u8=kani::any();kani::assume(row<25);
        let next:u8=kani::any(); let initial:[u8;32]=kani::any();
        let limbs:[[u32;4];25]=kani::any();
        let sem=limbs.map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}});
        let bytes:[u8;N]=kani::any();let len:usize=if N==0 {0} else {kani::any()};kani::assume(len<=N);
        let record=bytes[..len].to_vec();
        let oracle=RefCell::new(OracleState{answers:kani::any(),calls:Vec::new(),next:0,replay:false});
        let state=crate::r1_wire::make_kani29(Oracle(&oracle),initial,next);
        let actual=shipped_iteration(state,row,record.clone(),sem);
        let calls=oracle.borrow().next;
        let samples=unsafe {let n=SAMPLE_NEXT;SAMPLE_NEXT=0;SAMPLE_REPLAY=true;n};
        {let mut s=oracle.borrow_mut();s.next=0;s.replay=true;}
        let state=crate::r1_wire::make_kani29(Oracle(&oracle),initial,next);
        let reference=owned29::semantic_step(state,row,record,sem);
        assert_eq!(oracle.borrow().next,calls);
        assert_eq!(unsafe {SAMPLE_NEXT},samples);
        match (actual,reference) {
            (Ok((a,x)),Ok((b,y)))=>{assert_eq!(a.state(),b.state());assert_eq!(a.next_row(),b.next_row());assert_eq!(x,y);}
            (Err(a),Err(b))=>assert_eq!(a,b),
            _=>assert!(false),
        }
    }
    #[kani::proof] #[kani::stub(crate::sampler::qm31_sample,shared_sample)] #[kani::unwind(40)] fn empty_record(){check::<0>()}
    #[kani::proof] #[kani::stub(crate::sampler::qm31_sample,shared_sample)] #[kani::unwind(904)] fn all_semantic_records(){check::<901>()}
}

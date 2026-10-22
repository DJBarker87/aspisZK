#[cfg(kani)]
mod caller_kani30 {
    use super::*;
    #[derive(Clone,Copy)]
    pub struct Oracle<'a>(&'a RefCell<OracleState<'a>>);
    pub struct OracleState<'a> {
        answers:[[u8;32];3], initial:[u8;32], row:u8, record:&'a[u8], next:usize,
    }
    impl Digest32 for Oracle<'_> {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let mut s=self.0.borrow_mut();
            let i=s.next; assert!(i<3);
            if i==0 {
                assert_eq!(parts.len(),3);
                assert_eq!(parts[0],&s.initial);
                assert_eq!(parts[1],&[0,0xa0+s.row]);
                assert_eq!(parts[2].len(),s.record.len());if !s.record.is_empty() {let k:usize=kani::any();kani::assume(k<s.record.len());assert_eq!(parts[2][k],s.record[k]);}
            } else {
                assert_eq!(parts.len(),2);
                assert_eq!(parts[0],&s.answers[0]);
                assert_eq!(parts[1],&[i as u8]);
            }
            s.next+=1; s.answers[i]
        }
    }
    // Filled verbatim from the single native loop statement by install-kani.py.
    fn shipped_iteration<H:Digest32>(mut st:SemanticTranscript<H>, row:u8,
        r:&Records,mut sem:[K;25])->Result<(SemanticTranscript<H>,[K;25]),Error> {
        sem[row as usize]=st.semantic(row,&r.semantic[row as usize]).map_err(|_|Error::Semantic)?;
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
    fn checked_fields(row:u8,payload:Vec<u8>,value:usize)->Result<(),crate::r1_wire::Error> {
        let remaining=if row==14 {1} else {28};
        assert!(payload.len()<32*(remaining+1));
        assert_eq!(value,0);
        crate::r1_wire::fields29::finite(row,payload,value,remaining)
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
        let oracle=RefCell::new(OracleState{answers:kani::any(),initial,row,record:&bytes[..len],next:0});
        let state=crate::r1_wire::make_kani29(Oracle(&oracle),initial,next);
        let r=Records{c1_root:[0;32],semantic:(0..27usize).map(|i|if i==row as usize {record.clone()} else {Vec::new()}).collect(),
            y1:Vec::new(),inactive:[0;32],c0:Vec::new(),folded_root:[0;32],c1:Vec::new(),fin:Vec::new()};
        crate::r1_wire::modular_kani30::setup(record.clone(),row);
        let actual=shipped_iteration(state,row,&r,sem);
        let calls=oracle.borrow().next;let field_calls=crate::r1_wire::modular_kani30::count_reset();
        let samples=unsafe {let n=SAMPLE_NEXT;SAMPLE_NEXT=0;SAMPLE_REPLAY=true;n};
        oracle.borrow_mut().next=0;
        let state=crate::r1_wire::make_kani29(Oracle(&oracle),initial,next);
        let reference=owned29::iteration(state,row,r.semantic,sem);
        assert_eq!(oracle.borrow().next,calls);assert_eq!(crate::r1_wire::modular_kani30::count_reset(),field_calls);
        assert_eq!(unsafe {SAMPLE_NEXT},samples);
        match (actual,reference) {
            (Ok((a,x)),Ok((b,y)))=>{assert_eq!(a.state(),b.state());assert_eq!(a.next_row(),b.next_row());assert_eq!(x,y);}
            (Err(a),Err(b))=>assert_eq!(a,b),
            _=>assert!(false),
        }
    }
    #[kani::proof] #[kani::stub(crate::sampler::qm31_sample,shared_sample)]
    #[kani::stub(crate::r1_wire::fields20::validate,crate::r1_wire::modular_kani30::fields)]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::modular_kani30::summary)]
    #[kani::unwind(40)] fn all_rows(){check::<901>()}
}

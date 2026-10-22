#[cfg(kani)]
mod semantic_kani30 {
    use super::*;
    use core::cell::RefCell;
    #[derive(Clone,Copy)]
    struct Oracle<'a>(&'a RefCell<Log<'a>>);
    struct Log<'a> { answers:[[u8;32];3],initial:[u8;32],row:u8,record:&'a[u8],next:usize }
    impl Digest32 for Oracle<'_> {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let mut s=self.0.borrow_mut();let i=s.next;assert!(i<3);
            if i==0 {assert_eq!(parts.len(),3);assert_eq!(parts[0],&s.initial);
                assert_eq!(parts[1],&[0,0xa0+s.row]);assert_eq!(parts[2],s.record);}
            else {assert_eq!(parts.len(),2);assert_eq!(parts[0],&s.answers[0]);assert_eq!(parts[1],&[i as u8]);}
            s.next+=1;s.answers[i]
        }
    }
    static mut INPUT:[u8;32]=[0;32];static mut OUTPUT:QM31=QM31::ZERO;
    static mut COUNT:usize=0;static mut REPLAY:bool=false;
    fn sample(block:&[u8;32])->QM31 {unsafe {
        if REPLAY {assert_eq!(*block,INPUT);} else {INPUT=*block;}
        COUNT+=1;OUTPUT
    }}
    fn fields(row:u8,payload:Vec<u8>,value:usize)->Result<(),Error> {
        assert_eq!(value,0);assert!(payload.len()<32*29);
        fields29::finite(row,payload,value,28)
    }
    fn check<const N:usize,const ROW:u8>() {
        let initial:[u8;32]=kani::any();let next:u8=kani::any();
        let bytes:[u8;N]=kani::any();let len:usize=kani::any();kani::assume(len<=N);
        let record=&bytes[..len];let log=RefCell::new(Log{answers:kani::any(),initial,row:ROW,record,next:0});
        let x:[u32;4]=kani::any();
        unsafe {OUTPUT=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(x[0]),b:aspis_core::field::M31(x[1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(x[2]),b:aspis_core::field::M31(x[3])}};COUNT=0;REPLAY=false;}
        let mut native=SemanticTranscript{hash:Oracle(&log),state:initial,next_row:next};
        let a=native.semantic(ROW,record);let calls=log.borrow().next;
        let samples=unsafe {let n=COUNT;COUNT=0;REPLAY=true;n};log.borrow_mut().next=0;
        let owned=SemanticTranscript{hash:Oracle(&log),state:initial,next_row:next};
        let (b,after)=semantic20::semantic(owned,ROW,record.to_vec());
        assert_eq!(a,b);assert_eq!(native.state,after.state);assert_eq!(native.next_row,after.next_row);
        assert_eq!(log.borrow().next,calls);assert_eq!(unsafe{COUNT},samples);
        if a.is_err() {assert_eq!(calls,0);assert_eq!(native.state,initial);assert_eq!(native.next_row,next);}
        else {assert_eq!(calls,3);assert_eq!(samples,1);assert_eq!(native.state,log.borrow().answers[2]);assert_eq!(native.next_row,ROW+1);}
    }
    #[kani::proof] #[kani::stub(crate::sampler::qm31_sample,sample)] #[kani::stub(fields20::validate,fields)] #[kani::unwind(30)] fn row14(){check::<37,14>()}
    #[kani::proof] #[kani::stub(crate::sampler::qm31_sample,sample)] #[kani::stub(fields20::validate,fields)] #[kani::unwind(30)] fn row15(){check::<901,15>()}
}

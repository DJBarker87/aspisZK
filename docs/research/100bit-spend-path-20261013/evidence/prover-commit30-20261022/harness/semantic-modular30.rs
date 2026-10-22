#[cfg(kani)]
pub(crate) mod modular_kani30 {
    use super::*;
    use core::cell::RefCell;
    #[derive(Clone,Copy)]
    struct Oracle<'a>(&'a RefCell<Log<'a>>);
    struct Log<'a> { answers:[[u8;32];3],initial:[u8;32],row:u8,record:&'a[u8],next:usize }
    impl Digest32 for Oracle<'_> {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let mut s=self.0.borrow_mut();let i=s.next;assert!(i<3);
            if i==0 {assert_eq!(parts.len(),3);assert_eq!(parts[0],&s.initial);
                assert_eq!(parts[1],&[0,0xa0+s.row]);assert_eq!(parts[2].len(),s.record.len());if !s.record.is_empty() {let k:usize=kani::any();kani::assume(k<s.record.len());assert_eq!(parts[2][k],s.record[k]);}}
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
    static mut FIELD_RECORD:Vec<u8>=Vec::new();
    static mut FIELD_ROW:u8=0;
    static mut FIELD_RESULT:Result<(),Error>=Ok(());
    static mut FIELD_COUNT:usize=0;
    fn validation(row:u8,payload:&[u8])->Result<(),Error> {unsafe {
        assert_eq!(row,FIELD_ROW);assert_eq!(payload.len(),FIELD_RECORD.len()-5);
        assert!(payload.len()==32 || payload.len()==896);
        let k:usize=kani::any();kani::assume(k<payload.len());
        assert_eq!(payload[k],FIELD_RECORD[5+k]);
        FIELD_COUNT+=1;FIELD_RESULT
    }}
    pub(crate) fn fields(row:u8,payload:Vec<u8>,value:usize)->Result<(),Error> {
        assert_eq!(value,0);validation(row,&payload)
    }
    pub(crate) fn setup(record:Vec<u8>,row:u8) {unsafe {
        FIELD_RECORD=record;FIELD_ROW=row;FIELD_COUNT=0;
        FIELD_RESULT=if kani::any() {Ok(())} else {Err(Error::NonCanonical{row,value:kani::any()})};
    }}
    pub(crate) fn count_reset()->usize {unsafe {let n=FIELD_COUNT;FIELD_COUNT=0;n}}
    // Borrowed presentation of the independently checked owned semantic body.
    pub(crate) fn summary<H:Digest32>(state:&mut SemanticTranscript<H>,row:u8,record:&[u8])->Result<QM31,Error> {
        if row>24 {return Err(Error::InvalidRow);}
        if row!=state.next_row {return Err(Error::RowOrder{expected:state.next_row,actual:row});}
        semantic20::checked(row,record)?;
        let block=state.sample_block_validated(row,record)?;
        Ok(crate::sampler::qm31_sample(&block))
    }
    fn check<const N:usize>(row:u8) {
        let initial:[u8;32]=kani::any();let next:u8=kani::any();
        let bytes:[u8;N]=kani::any();let len:usize=kani::any();kani::assume(len<=N);
        let record=&bytes[..len];let log=RefCell::new(Log{answers:kani::any(),initial,row,record,next:0});
        unsafe {FIELD_RECORD=record.to_vec();FIELD_ROW=row;FIELD_COUNT=0;
            FIELD_RESULT=if kani::any() {Ok(())} else {Err(Error::NonCanonical{row,value:kani::any()})};}
        let x:[u32;4]=kani::any();
        unsafe {OUTPUT=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(x[0]),b:aspis_core::field::M31(x[1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(x[2]),b:aspis_core::field::M31(x[3])}};COUNT=0;REPLAY=false;}
        let mut native=SemanticTranscript{hash:Oracle(&log),state:initial,next_row:next};
        let a=native.semantic(row,record);let calls=log.borrow().next;let validation_calls=unsafe {let n=FIELD_COUNT;FIELD_COUNT=0;n};
        let samples=unsafe {let n=COUNT;COUNT=0;REPLAY=true;n};log.borrow_mut().next=0;
        let owned=SemanticTranscript{hash:Oracle(&log),state:initial,next_row:next};
        let (b,after)=semantic20::semantic(owned,row,record.to_vec());
        assert_eq!(unsafe{FIELD_COUNT},validation_calls);assert_eq!(a,b);assert_eq!(native.state,after.state);assert_eq!(native.next_row,after.next_row);
        assert_eq!(log.borrow().next,calls);assert_eq!(unsafe{COUNT},samples);
        let field_calls=count_reset();log.borrow_mut().next=0;unsafe{COUNT=0;}
        let mut summarized=SemanticTranscript{hash:Oracle(&log),state:initial,next_row:next};
        let c=summary(&mut summarized,row,record);
        assert_eq!(a,c);assert_eq!(native.state,summarized.state);assert_eq!(native.next_row,summarized.next_row);
        assert_eq!(log.borrow().next,calls);assert_eq!(unsafe{COUNT},samples);assert_eq!(count_reset(),field_calls);
        if a.is_err() {assert_eq!(calls,0);assert_eq!(native.state,initial);assert_eq!(native.next_row,next);}
        else {assert_eq!(calls,3);assert_eq!(samples,1);assert_eq!(native.state,log.borrow().answers[2]);assert_eq!(native.next_row,row+1);}
    }
    #[kani::proof] #[kani::stub(crate::sampler::qm31_sample,sample)]
    #[kani::stub(fields20::validate,fields)] #[kani::stub(validate_record_fields,validation)]
    #[kani::unwind(30)] fn all_rows(){let row:u8=kani::any();kani::assume(row<25);check::<901>(row)}
}

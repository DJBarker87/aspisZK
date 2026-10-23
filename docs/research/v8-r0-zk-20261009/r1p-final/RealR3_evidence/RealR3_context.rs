#[cfg(kani)]
pub(crate) mod RealR3_context {
    use super::*;
    static mut RECORD:Vec<u8>=Vec::new();
    static mut ROW:u8=0;
    static mut BEFORE:[u8;32]=[0;32];static mut NEXT:u8=0;
    static mut AFTER:[u8;32]=[0;32];static mut AFTER_NEXT:u8=0;
    static mut RESULT:Result<QM31,Error>=Ok(QM31::ZERO);
    static mut CALLS:usize=0;
    pub(crate) fn setup(record:Vec<u8>,row:u8,before:[u8;32],next:u8,value:QM31) {unsafe {
        RECORD=record;ROW=row;BEFORE=before;NEXT=next;CALLS=0;
        AFTER=kani::any();AFTER_NEXT=kani::any();
        let error=match kani::any::<u8>() {
            0=>Error::Allocation,1=>Error::RowOrder{expected:kani::any(),actual:kani::any()},
            2=>Error::InvalidRow,3=>Error::Tag{row:kani::any()},4=>Error::Length{row:kani::any()},
            5=>Error::NonCanonical{row:kani::any(),value:kani::any()},6=>Error::Boundary{round:kani::any()},
            7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,10=>Error::Public,
            _=>Error::ActivePole,
        };
        RESULT=if kani::any() {Ok(value)} else {Err(error)};
    }}
    pub(crate) fn count_reset()->usize {unsafe{let n=CALLS;CALLS=0;n}}
    fn apply<H:Digest32>(st:&mut SemanticTranscript<H>,row:u8,record:&[u8])->Result<QM31,Error> {unsafe {
        assert_eq!(row,ROW);assert_eq!(st.state,BEFORE);assert_eq!(st.next_row,NEXT);
        assert_eq!(record.len(),RECORD.len());
        if !record.is_empty() {let k:usize=kani::any();kani::assume(k<record.len());assert_eq!(record[k],RECORD[k]);}
        CALLS+=1;st.state=AFTER;st.next_row=AFTER_NEXT;RESULT
    }}
    pub(crate) fn native<H:Digest32>(st:&mut SemanticTranscript<H>,row:u8,record:&[u8])->Result<QM31,Error> {
        apply(st,row,record)
    }
    pub(crate) fn owned<H:Digest32>(mut st:SemanticTranscript<H>,row:u8,record:Vec<u8>)
        ->(Result<QM31,Error>,SemanticTranscript<H>) {
        let out=apply(&mut st,row,&record);(out,st)
    }
    static mut FIELD_RESULT:Result<(),Error>=Ok(());
    static mut FIELD_CALLS:usize=0;
    pub(crate) fn setup_fields(){unsafe{
        assert_eq!(ROW,15);assert_eq!(RECORD.len(),901);FIELD_CALLS=0;
        FIELD_RESULT=if kani::any(){Ok(())}else{Err(Error::NonCanonical{row:ROW,value:kani::any()})};
    }}
    pub(crate) fn field_count_reset()->usize{unsafe{let n=FIELD_CALLS;FIELD_CALLS=0;n}}
    pub(crate) fn fields(row:u8,payload:&[u8])->Result<(),Error>{unsafe{
        assert_eq!(row,ROW);assert_eq!(payload.len(),RECORD.len()-5);assert_eq!(payload.len(),896);
        let j:usize=kani::any();kani::assume(j<payload.len());assert_eq!(payload[j],RECORD[5+j]);
        FIELD_CALLS+=1;FIELD_RESULT
    }}
}

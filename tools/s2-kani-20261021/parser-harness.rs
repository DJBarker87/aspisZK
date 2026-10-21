fn record_range(row:u8)->(usize,usize) {
    let mut i=0u8;let mut at=32usize;
    while i<row {at+=5+row_shape(i).unwrap().1;i+=1;}
    (at,5+row_shape(row).unwrap().1)
}
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof] #[kani::unwind(29)] fn prefix_records_are_reached_slices(){
    unsafe{FAIL_ROW=255;}
    let bytes=[0u8;13831];let row:u8=kani::any();kani::assume(row<27);
    let p=Prefix::parse(&bytes).unwrap();
    let (at,length)=record_range(row);
    let rec=p.record(row).unwrap();
    assert_eq!(rec.as_ptr(),bytes[at..at+length].as_ptr());assert_eq!(rec.len(),length);
    let token=p.validated_record(row).unwrap();
    assert_eq!(token.row,row);assert_eq!(token.framed.as_ptr(),rec.as_ptr());assert_eq!(token.framed.len(),rec.len());
    assert_eq!(p.payload(row).unwrap().as_ptr(),bytes[at+5..at+length].as_ptr());
    assert_eq!(p.payload(row).unwrap().len(),length-5);
    if row==25 {assert_eq!((at,length),(9181,3717));}
    if row==26 {assert_eq!((at,length),(12898,933));}
}
#[kani::proof] #[kani::unwind(29)] fn prefix_propagates_first_parser_error(){
    let row:u8=kani::any();kani::assume(row<27);unsafe{FAIL_ROW=row;}
    let bytes=[0u8;13831];
    assert!(matches!(Prefix::parse(&bytes),Err(Error::Rejected{row:r}) if r==row));
}
#[kani::proof] #[kani::unwind(29)] fn record_at_exact_range(){
    let row:u8=kani::any();kani::assume(row<27);unsafe{FAIL_ROW=255;}
    let bytes=[0u8;13831];let (at,length)=record_range(row);
    let (framed,next)=parse_record_at(&bytes,row,at).unwrap();
    assert_eq!(next,at+length);assert_eq!(framed.as_ptr(),bytes[at..].as_ptr());assert_eq!(framed.len(),length);
}
}

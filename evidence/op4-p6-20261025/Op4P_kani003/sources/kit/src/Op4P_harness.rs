use super::{Op4P_reference as r,Op4P_shipped as s};
// Start with the complete opening loop body rather than normalize the whole
// 57,607-byte scanner in one CBMC formula.
#[kani::proof]
#[kani::unwind(160)]
fn Op4P_opening() {
    let bytes:[u8;832]=kani::any();
    assert_eq!(s::opening_body(&bytes),
        if r::parser_reference::opening_scan(&bytes) {Ok(())} else {Err(r::Error::Parse)});
}

#[kani::proof]
#[kani::unwind(34)]
fn Op4P_y1() {
    let bytes:[u8;464]=kani::any();
    assert_eq!(s::compact::check_values(&bytes).is_ok(),r::reference::check_values(&bytes));
}
#[kani::proof]
#[kani::unwind(18)]
fn Op4P_wide_step() {
    let bytes:[u8;32]=kani::any();
    assert_eq!(s::echeck(&bytes,false),
        if r::parser_reference::canonical_words(&bytes) {Ok(())} else {Err(r::Error::Parse)});
}
#[kani::proof]
fn Op4P_opening_address() {
    let bytes:[u8;57607]=kani::any();
    let i:usize=kani::any(); let j:usize=kani::any();
    kani::assume(i<22 && j<832);
    let q=s::opening(&bytes,i);
    assert_eq!(q.len(),832);
    assert_eq!(q[j],bytes[10055+i*832+j]);
}
// Whole scan has no oracle/allocator/mutable input operation; the only error
// propagated by every reached decoder is Parse. These continuations cover both
// outcomes, including short-circuit rejection with no remaining effect.
#[kani::proof]
fn Op4P_result_continuation() {
    let a:bool=kani::any();let b:bool=kani::any();
    let left:Result<(),r::Error>=(||{
        if !a {return Err(r::Error::Parse);}
        if !b {return Err(r::Error::Parse);}
        Ok(())
    })();
    assert_eq!(left,if a && b {Ok(())} else {Err(r::Error::Parse)});
}

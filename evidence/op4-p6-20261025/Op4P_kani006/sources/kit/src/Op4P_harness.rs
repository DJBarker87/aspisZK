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

// Every chunks_exact(32) iteration in all three shipped wide regions, at
// arbitrary ordinal and observation coordinate, over arbitrary deployed bytes.
#[kani::proof]
#[kani::unwind(74)]
fn Op4P_wide_chunks() {
    let bytes:[u8;57607]=kani::any();
    let region:u8=kani::any(); kani::assume(region<3);
    let (start,end)=match region {0=>(7495,7527),1=>(7527,7751),_=>(7783,10055)};
    let i:usize=kani::any();let j:usize=kani::any();
    kani::assume(i<(end-start)/32 && j<32);
    let mut chunks=bytes[start..end].chunks_exact(32);
    assert_eq!(chunks.len(),(end-start)/32);
    assert_eq!(chunks.remainder().len(),0);
    let c=chunks.nth(i).unwrap();
    assert_eq!(c.len(),32);
    assert_eq!(c[j],bytes[start+32*i+j]);
    assert_eq!(chunks.len(),(end-start)/32-i-1);
}

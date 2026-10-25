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

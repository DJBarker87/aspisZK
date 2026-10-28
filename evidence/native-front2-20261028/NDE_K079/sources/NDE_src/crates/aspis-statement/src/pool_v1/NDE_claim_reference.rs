// The body is identical to extracted NDE_Reference4.claim_ref. This type alias
// instantiates its four-word carrier with the frozen native carrier.
use aspis_core::field::QM31 as Q;
pub fn claim_ref(claims:&[Q;84],point:usize,column:usize)->Q{claims[point*28+column]}

use aspis_core::field::WideExact as E;
use super::{FIn_native as s,FIn_reference as r};
#[kani::proof]
#[kani::unwind(9)]
fn FIn_polynomial() {
    let bytes:[u8;224]=kani::any();
    // The actual installed scanner guarantees these seven decoders succeed.
    // There is no honest-coefficient or honest-challenge restriction.
    for i in 0..7 {kani::assume(E::from_le_bytes(&bytes[32*i..32*(i+1)]).is_some());}
    let xb:[u8;32]=kani::any();
    let x=E::from_le_bytes(&xb); kani::assume(x.is_some()); let x=x.unwrap();
    assert_eq!(s::polynomial(&bytes,x),r::polynomial::<s::Native>(&bytes,x));
}

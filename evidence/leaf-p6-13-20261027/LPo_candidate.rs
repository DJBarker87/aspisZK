use super::*;
// One selected observation of the actual native call, not a whole-buffer comparison.
fn range<const PART: usize>() {
    let p: [u8; compact::PROOF_BYTES] = kani::any();
    let semantic: [u8; compact::LOGICAL_SEMANTIC] = kani::any();
    let y1: [u8; compact::LOGICAL_Y1] = kani::any();
    let sem_len: usize = kani::any(); let y_len: usize = kani::any();
    kani::assume(sem_len <= semantic.len() && y_len <= y1.len());
    let s = &semantic[..sem_len]; let y = &y1[..y_len];
    let sp = s.as_ptr(); let yp = y.as_ptr();
    let inactive = E::from_le_bytes(&p[compact::OFF_INACTIVE..compact::OFF_ROUND0]);
    let got = wide_view(&p, s, y);
    match (got, inactive) {
        (Err(e), None) => assert_eq!(e, Error::Parse),
        (Ok(v), Some(e)) => {
            if PART == 0 { assert_eq!(v.inactive, e); assert!(matches!(v.variant, Variant::S2)); assert_eq!(v.query_bytes.len(), 0); }
            if PART == 1 { assert_eq!(v.round0.len(), 224); assert!(core::ptr::eq(v.round0.as_ptr(), p[7527..7751].as_ptr())); }
            if PART == 2 { let r = v.folded_root.unwrap(); let i: usize = kani::any(); kani::assume(i < 32); assert_eq!(r[i], p[7751+i]); }
            if PART == 3 { assert_eq!(v.round1.len(), 224); assert!(core::ptr::eq(v.round1.as_ptr(), p[7783..8007].as_ptr())); }
            if PART == 4 { assert_eq!(v.final_message.len(), 2048); assert!(core::ptr::eq(v.final_message.as_ptr(), p[8007..10055].as_ptr())); }
            if PART == 5 { assert_eq!(v.semantic.len(), sem_len); assert_eq!(v.y1.len(), y_len); assert!(core::ptr::eq(v.semantic.as_ptr(), sp)); assert!(core::ptr::eq(v.y1.as_ptr(), yp)); }
        }
        _ => panic!("native inactive/result mismatch"),
    }
}
#[kani::proof] #[kani::unwind(10)] fn LPo_inactive() { range::<0>(); }
#[kani::proof] #[kani::unwind(10)] fn LPo_round0() { range::<1>(); }
#[kani::proof] #[kani::unwind(10)] fn LPo_root() { range::<2>(); }
#[kani::proof] #[kani::unwind(10)] fn LPo_round1() { range::<3>(); }
#[kani::proof] #[kani::unwind(10)] fn LPo_final() { range::<4>(); }
#[kani::proof] #[kani::unwind(10)] fn LPo_passthrough() { range::<5>(); }

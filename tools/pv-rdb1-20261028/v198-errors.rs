use aspis_core::field::{QM31, CM31, M31};
use std::panic::{catch_unwind,AssertUnwindSafe};
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut pairs=0;
    let mut partial=0;
    for w in [0u32,1,u32::MAX,0x80000000,0x12345678] {
        let limbs=[w,w.rotate_left(8),!w,w.wrapping_add(1)];
        let x=QM31{c0:CM31{a:M31(limbs[0]),b:M31(limbs[1])},c1:CM31{a:M31(limbs[2]),b:M31(limbs[3])}};
        let encoded:Vec<u8>=limbs.iter().flat_map(|v|v.to_le_bytes()).collect();
        for n in 0..=24 {
            let mut actual=vec![0xa5;n];
            let initial=actual.clone();
            let result=catch_unwind(AssertUnwindSafe(||x.write_le_bytes(&mut actual)));
            assert_eq!(result.is_ok(),n>=16);
            let mut expected=initial.clone();
            if n>=8 {expected[..8].copy_from_slice(&encoded[..8]);}
            if n>=16 {expected[8..16].copy_from_slice(&encoded[8..16]);}
            assert_eq!(actual,expected);
            if (8..16).contains(&n) {assert_ne!(actual,initial);partial+=1;}
            pairs+=1;
        }
    }
    println!("PASS V198 {pairs} complete status/buffer pairs, including {partial} partial-write panics; finite validation only");
}

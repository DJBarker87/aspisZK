#![allow(unexpected_cfgs)]
#[cfg(kani)]
pub type Q = [[u32; 2]; 2];
#[cfg(kani)]
pub fn equal(a: Q, b: Q) -> bool {
    ((a[0][0] ^ b[0][0]) | (a[0][1] ^ b[0][1]) |
     (a[1][0] ^ b[1][0]) | (a[1][1] ^ b[1][1])) == 0
}
#[cfg(kani)]
pub fn keep_clear(clear: bool, active: bool, chi: Q, value: Q) -> bool {
    clear & !(active & equal(chi, value))
}
#[cfg(kani)]
pub fn scan(values: &[[[Q; 2]; 2]], masks: &[u16; 64], chi: Q) -> bool {
    let mut clear = true;
    let mut row = 0usize;
    while row < values.len() {
        let active = masks[row >> 4] & (1 << (row & 15)) != 0;
        let mut side = 0usize;
        while side < 2 {
            let mut slot = 0usize;
            while slot < 2 {
                clear = keep_clear(clear, active, chi, values[row][side][slot]);
                slot += 1;
            }
            side += 1;
        }
        row += 1;
    }
    clear
}
#[cfg(all(kani, not(pv_join_extract)))]
#[path = "ct_pole.rs"]
mod shipped;
#[cfg(all(kani, not(pv_join_extract)))]
mod checks {
    use super::*;
    use aspis_core::field::{QM31, CM31, M31};
    fn encode(a: Q) -> QM31 {
        QM31 {c0: CM31 {a: M31(a[0][0]), b: M31(a[0][1])},
              c1: CM31 {a: M31(a[1][0]), b: M31(a[1][1])}}
    }
    #[kani::proof]
    fn equal_raw() {
        let a: Q = kani::any(); let b: Q = kani::any();
        assert_eq!(shipped::equal(encode(a), encode(b)), equal(a,b));
    }
    #[kani::proof]
    fn keep_clear_raw() {
        let a: Q = kani::any(); let b: Q = kani::any();
        let clear: bool = kani::any(); let active: bool = kani::any();
        assert_eq!(shipped::keep_clear(clear,active,encode(a),encode(b)),
                   keep_clear(clear,active,a,b));
    }
    #[kani::proof]
    #[kani::unwind(1026)]
    fn scan_1024_raw() {
        let raw: [[[Q; 2]; 2]; 1024] = kani::any();
        let masks: [u16; 64] = kani::any(); let chi: Q = kani::any();
        let len: usize = kani::any(); kani::assume(len <= 1024);
        let mut values = [[[QM31::ZERO; 2]; 2]; 1024];
        let mut row = 0;
        while row < 1024 {
            let mut side = 0;
            while side < 2 {
                let mut slot = 0;
                while slot < 2 {
                    values[row][side][slot] = encode(raw[row][side][slot]);
                    slot += 1;
                }
                side += 1;
            }
            row += 1;
        }
        assert_eq!(shipped::all_slots_clear(&values[..len], &masks, encode(chi)),
                   scan(&raw[..len], &masks, chi));
    }
}
#[cfg(kani)]
pub fn empty<T>() -> Vec<T> { Vec::new() }
#[cfg(all(kani, not(pv_join_extract)))]
mod row_counterexample {
    use aspis_core::field::{QM31,CM31,M31};
    use aspis_core::state_only_sumcheck::{evaluate_state_only_polynomial as source,
        evaluate_state_only_polynomial_horner as reference};
    fn q(a:u32,b:u32,c:u32,d:u32)->QM31 {
        QM31{c0:CM31{a:M31(a),b:M31(b)},c1:CM31{a:M31(c),b:M31(d)}}
    }
    #[kani::proof]
    #[kani::unwind(40)]
    fn poly_raw_exact() {
        let mut polynomial=[QM31::ZERO;28];
        polynomial[2]=q(1,0,0,0);
        let challenge=q(0,2147483648,0,0);
        let actual=source(&polynomial,challenge);
        let expected=reference(&polynomial,challenge);
        assert_eq!(actual,q(3,0,0,0));
        assert_eq!(expected,q(2147483646,0,0,0));
        assert_ne!(actual,expected);
    }
}

#[cfg(all(kani, not(pv_join_extract)))]
mod reference_counterexample {
    use aspis_core::field::{QM31,CM31,M31};
    #[kani::proof]
    #[kani::unwind(40)]
    fn poly_reference_raw_exact() {
        let mut polynomial=[QM31::ZERO;28];
        polynomial[2]=QM31::ONE;
        let challenge=QM31{c0:CM31{a:M31(0),b:M31(2147483648)},c1:CM31::ZERO};
        let value=aspis_core::state_only_sumcheck::evaluate_state_only_polynomial_horner(&polynomial,challenge);
        let expected=QM31{c0:CM31{a:M31(2147483646),b:M31(0)},c1:CM31::ZERO};
        assert_eq!(value,expected);
    }
}

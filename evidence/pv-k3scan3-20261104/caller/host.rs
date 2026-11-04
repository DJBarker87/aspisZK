use aspis_core::field::{QM31,CM31,M31};
#[derive(Clone,Copy)] struct Selectors {high:[QM31;64],low:[QM31;16]}
fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>]) -> QM31 {
    let mut sum = QM31::ZERO;
    for range in ranges {
        for block in range.clone() {
            sum = sum.add(selectors.high[block]);
        }
    }
    sum
}
pub fn sum(h:[QM31;64],l:[QM31;16],r:&[core::ops::Range<usize>])->QM31 { sum_high(&Selectors{high:h,low:l},r) }

use aspis_core::field::{QM31,CM31,M31};
#[derive(Clone,Copy)] struct Selectors {high:[QM31;64],low:[QM31;16]}
fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>]) -> QM31 {
    let mut sum = QM31::ZERO;
    let mut range_index = 0usize;
    while range_index < ranges.len() {
        let mut block = ranges[range_index].start;
        while block < ranges[range_index].end {
            sum = sum.add(selectors.high[block]);
            block += 1;
        }
        range_index += 1;
    }
    sum
}
pub fn sum(h:[QM31;64],l:[QM31;16],r:&[core::ops::Range<usize>])->QM31 { sum_high(&Selectors{high:h,low:l},r) }

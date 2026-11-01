//! Secret-operand pole comparisons. Shape and masks are public registry data.
use aspis_core::field::QM31;

#[inline(always)]
pub(crate) fn equal(a: QM31, b: QM31) -> bool {
    let different = (a.c0.a.0 ^ b.c0.a.0)
        | (a.c0.b.0 ^ b.c0.b.0)
        | (a.c1.a.0 ^ b.c1.a.0)
        | (a.c1.b.0 ^ b.c1.b.0);
    different == 0
}

#[inline(always)]
pub(crate) fn keep_clear(clear: bool, active: bool, chi: QM31, value: QM31) -> bool {
    clear & !(active & equal(chi, value))
}

pub(crate) fn all_slots_clear(values: &[[[QM31; 2]; 2]], masks: &[u16; 64], chi: QM31) -> bool {
    let mut clear = true;
    for (row, sides) in values.iter().enumerate() {
        let active = masks[row >> 4] & (1 << (row & 15)) != 0;
        for side in sides {
            for value in side {
                clear = keep_clear(clear, active, chi, *value);
            }
        }
    }
    clear
}

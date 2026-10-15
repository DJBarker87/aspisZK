#![no_std]
#![allow(dead_code)]
pub mod r1_wire {
pub const LANES: usize = 29;
pub const POINTS: usize = 3;
pub const CLAIMS: usize = POINTS * LANES;
/// P1 tag and exact payload length, including the message-free rows.
pub const fn row_shape(row: u8) -> Option<(u8, usize)> {
    match row {
        0 | 1 | 3..=13 => Some((0, 0)),
        2 => Some((1, 32)),
        14 => Some((3, 32)),
        15..=24 => Some((2, 28 * 32)),
        25 => Some((4, (CLAIMS + LANES) * 32)),
        26 => Some((5, LANES * 32)),
        _ => None,
    }
}
}

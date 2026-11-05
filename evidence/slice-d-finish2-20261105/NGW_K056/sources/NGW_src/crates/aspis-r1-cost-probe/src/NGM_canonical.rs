use super::Dot;
pub(in crate::fast_pairing) fn read(dot:&Dot)->[u64;4]{dot.sums}
pub(in crate::fast_pairing) fn make(sums:[u64;4])->Dot{Dot{sums}}

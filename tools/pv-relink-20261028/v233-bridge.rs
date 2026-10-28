// Proof-only appended access to the unchanged private Sealed body.
pub fn pv_rl_split(data:&[u8])->(&[Block<generic_array::typenum::U64>],&[u8]) {
 <Eager as sealed::Sealed>::split_blocks::<generic_array::typenum::U64>(data)
}

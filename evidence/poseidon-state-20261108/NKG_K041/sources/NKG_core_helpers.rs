#[cfg(kani)]
pub fn NKG_prepared_from_words(words:[[u32;3];3])->PreparedQm31Multiplier {
 PreparedQm31Multiplier{components:words.map(|r|r.map(M31))}
}
#[cfg(kani)]
pub fn NKG_prepared_words(value:PreparedQm31Multiplier)->[[u32;3];3] {
 value.components.map(|r|r.map(|x|x.0))
}

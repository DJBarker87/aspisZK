// Proof-only sibling access; original field.rs remains an unchanged prefix.
pub fn pv_rl_bytes(w:[u32;8])->([u8;32],[u8;32]) { wide_exact::pv_rl_checks::native_and_reference(w) }

//! P6 reference for the isolated native shared-zero scan. Not shipped code.
pub fn zero_bytes(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != 0 { return false; }
        i += 1;
    }
    true
}

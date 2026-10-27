//! P6 reference for the isolated native shared-zero scan. Not shipped code.
pub fn zero_bytes(bytes: &[u8]) -> bool {
    let mut i = 0;
    let mut zero = true;
    while i < bytes.len() && zero {
        zero = bytes[i] == 0;
        i += 1;
    }
    zero
}

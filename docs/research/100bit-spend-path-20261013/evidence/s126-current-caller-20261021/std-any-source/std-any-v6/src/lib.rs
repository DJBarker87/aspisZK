pub fn checkpoint_nonzero(bytes: &[u8]) -> bool { bytes.iter().any(|byte| *byte != 0) }

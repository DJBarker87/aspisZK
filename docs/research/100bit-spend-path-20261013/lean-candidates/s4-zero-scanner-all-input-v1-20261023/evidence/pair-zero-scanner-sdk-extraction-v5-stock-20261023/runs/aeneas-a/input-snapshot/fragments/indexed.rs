fn require_zero(bytes: &[u8]) -> ProgramResult {
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        index += 1;
    }
    Ok(())
}

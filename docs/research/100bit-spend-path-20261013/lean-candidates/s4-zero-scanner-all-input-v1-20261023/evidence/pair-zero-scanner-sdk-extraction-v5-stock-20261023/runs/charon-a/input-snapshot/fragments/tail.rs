fn require_zero(mut remaining: &[u8]) -> ProgramResult {
    while !remaining.is_empty() {
        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        remaining = &remaining[1..];
    }
    Ok(())
}

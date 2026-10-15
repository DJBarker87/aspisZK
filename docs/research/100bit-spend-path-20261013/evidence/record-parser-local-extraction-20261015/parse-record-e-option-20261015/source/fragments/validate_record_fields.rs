fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
    for (value, bytes) in payload.chunks_exact(32).enumerate() {
        let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
        if x.c1() != QM31::ZERO {
            return Err(Error::NonCanonical { row, value });
        }
    }
    Ok(())
}
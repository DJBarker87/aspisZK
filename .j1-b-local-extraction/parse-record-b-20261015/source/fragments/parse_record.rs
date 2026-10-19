/// Reject malformed framing and every noncanonical E limb before hashing.
/// UNPROVED P2 subset: reject any nonzero E high component at parse.
pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if record.len() != 5 + size {
        return Err(Error::Length { row });
    }
    if record[0] != tag {
        return Err(Error::Tag { row });
    }
    if u32::from_le_bytes(record[1..5].try_into().unwrap()) as usize != size {
        return Err(Error::Length { row });
    }
    let payload = &record[5..];
    if row >= 14 {
        for (value, bytes) in payload.chunks_exact(32).enumerate() {
            let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
            if x.c1() != QM31::ZERO {
                return Err(Error::NonCanonical { row, value });
            }
        }
    }
    Ok(payload)
}
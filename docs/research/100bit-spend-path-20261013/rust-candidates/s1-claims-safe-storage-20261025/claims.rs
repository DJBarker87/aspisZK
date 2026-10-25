#[inline(never)]
fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
    let record = prefix.validated_record(25)?;
    let rows = aspis_core::r0::heap::filled(3, [QM31::ZERO; 29])
        .map_err(|_| Error::Allocation)?;
    let mut out: Box<[[QM31; 29]; 3]> = rows
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Error::Allocation)?;
    for p in 0..3 {
        out[p] = record.decode_k::<29>(p * 29)?;
    }
    Ok(out)
}

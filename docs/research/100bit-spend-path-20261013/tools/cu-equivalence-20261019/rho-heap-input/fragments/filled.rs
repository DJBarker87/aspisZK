pub fn filled<T: Copy>(n: usize, value: T) -> Result<Vec<T>, Error> {
    let mut out = Vec::new();
    out.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
    out.resize(n, value);
    Ok(out)
}
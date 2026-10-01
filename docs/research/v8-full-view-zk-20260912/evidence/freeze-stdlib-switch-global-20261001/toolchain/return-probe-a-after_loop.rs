pub fn after_loop(hit: bool, fail: bool) -> Result<u32, u8> {
    let mut second = None;
    for i in 0..3u32 {
        if hit { second = Some(i); break; }
    }
    let value = second.ok_or(8u8)?;
    if fail { Err::<(), u8>(7u8)?; }
    Ok(value)
}

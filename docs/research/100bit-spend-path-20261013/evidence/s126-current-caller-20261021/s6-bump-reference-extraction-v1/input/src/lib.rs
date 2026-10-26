pub fn step(initial: usize, length: usize, bytes: usize, align: usize) -> Option<usize> {
    let cursor = if initial == 0 { length } else { initial };
    let available = cursor.checked_sub(bytes)?;
    let next = (available / align) * align;
    if next < core::mem::size_of::<usize>() { None } else { Some(next) }
}

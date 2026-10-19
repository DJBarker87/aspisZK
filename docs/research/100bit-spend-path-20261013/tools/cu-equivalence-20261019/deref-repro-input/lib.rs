pub struct Guard<'a> {
    pub array_mut: &'a mut [u8],
    pub initialized: usize,
}

pub fn projected_len(guard: &mut Guard<'_>) -> usize {
    guard.array_mut.len()
}

pub fn explicit_len(guard: &mut Guard<'_>) -> usize {
    let values: &[u8] = &*guard.array_mut;
    values.len()
}

pub fn direct_len(values: &mut [u8]) -> usize {
    values.len()
}

pub struct Shared<'a> {
    pub array: &'a [u8],
}

pub fn shared_len(guard: &Shared<'_>) -> usize {
    guard.array.len()
}

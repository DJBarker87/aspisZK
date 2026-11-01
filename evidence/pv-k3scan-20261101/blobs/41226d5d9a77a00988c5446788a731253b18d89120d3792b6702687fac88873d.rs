// Independent noDrop printer/loan regression. The original Guard is unchanged.
pub struct Owner<'a> { pub slot: Option<&'a mut u32> }
pub fn increment(counter: &mut u32) { *counter = counter.wrapping_add(1); }
pub fn update(owner: &mut Owner<'_>) {
    if let Some(counter) = &mut owner.slot { increment(counter); }
}
pub fn writeback(counter: &mut u32) {
    let mut owner = Owner { slot: Some(counter) };
    update(&mut owner);
}
pub fn counter_probe() -> u32 { let mut n = 0; writeback(&mut n); n }
#[cfg(test)] mod tests {
    use super::*;
    #[test] fn reference_writeback() {
        assert_eq!(counter_probe(), 1);
        let mut n = u32::MAX; writeback(&mut n); assert_eq!(n, 0);
        update(&mut Owner {slot: None});
    }
}

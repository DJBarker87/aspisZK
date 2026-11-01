//! Minimal baseline regression; no refined errors or external dependencies.
pub struct Guard<'a> { pub counter: Option<&'a mut u32> }
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        let mut owned = None;
        core::mem::swap(&mut self.counter, &mut owned);
        if let Some(counter) = owned { increment(counter); }
    }
}
pub fn increment(counter: &mut u32) { *counter = (*counter).wrapping_add(1); }
pub fn real_drop(counter: &mut u32) {
    let _guard = Guard { counter: Some(counter) };
}
pub fn counter_probe() -> u32 {
    let mut counter = 0;
    real_drop(&mut counter);
    counter
}
#[cfg(test)]
mod tests {
    #[test]
    fn native_counter_zero_becomes_one() {
        assert_eq!(super::counter_probe(), 1);
    }
}

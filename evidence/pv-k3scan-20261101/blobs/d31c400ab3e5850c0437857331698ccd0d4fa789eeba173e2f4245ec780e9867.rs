// Isolated native-source probes. No provider installation.
pub struct Guard<'a> { pub code: getrandom::Error, pub counter: &'a mut u32 }
impl Drop for Guard<'_> {
    fn drop(&mut self) { *self.counter = self.counter.wrapping_add(1); }
}
pub fn real_drop(code: getrandom::Error, counter: &mut u32) {
    let _guard = Guard { code, counter };
}
pub fn live_borrow(code: &mut getrandom::Error) -> (getrandom::Error, &mut getrandom::Error) {
    let copied = *code;
    (copied, code)
}

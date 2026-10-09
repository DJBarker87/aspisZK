//! Passive, thread-local native trace. Never compiled into SBF.
extern crate std;
use crate::field::WideExact;
use alloc::vec::Vec;
std::thread_local! { static TRACE: std::cell::RefCell<Vec<[u8; 32]>> = const { std::cell::RefCell::new(Vec::new()) }; }
pub fn fields(values: &[WideExact]) {
    TRACE.with(|v| {
        v.borrow_mut()
            .extend(values.iter().map(|x| x.to_le_bytes()))
    });
}
pub fn take() -> Vec<[u8; 32]> {
    TRACE.with(|v| core::mem::take(&mut *v.borrow_mut()))
}

std::thread_local! { static REFERENCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
pub fn is_reference() -> bool {
    REFERENCE.with(|x| x.get())
}
pub struct ReferenceGuard(bool);
pub fn reference() -> ReferenceGuard {
    ReferenceGuard(REFERENCE.with(|x| x.replace(true)))
}
impl Drop for ReferenceGuard {
    fn drop(&mut self) {
        REFERENCE.with(|x| x.set(self.0));
    }
}

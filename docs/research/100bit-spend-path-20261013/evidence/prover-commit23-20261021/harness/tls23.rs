#[cfg(kani)]
mod tls23 {
    use super::*;
    type Trace = std::cell::RefCell<Vec<(u16, usize, [u8; 32])>>;
    // Runtime boundary: one thread, one live trace key, no thread exit or
    // key destruction during this invocation. RefCell borrow checks remain.
    // This replaces only LocalKey::with for this concrete T, not value/take.
    static mut SLOT: Trace = std::cell::RefCell::new(Vec::new());
    fn single_with<T: 'static, F, R>(_: &std::thread::LocalKey<T>, f: F) -> R
    where F: FnOnce(&T) -> R {
        unsafe { f(&*(core::ptr::addr_of!(SLOT) as *const T)) }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(std::thread::LocalKey::with, single_with)]
    fn append_take() {
        let tag:u16=kani::any();let index:usize=kani::any();
        let _prior=crate::trace::take();
        crate::trace::value(tag,index,E::ZERO);
        let actual=crate::trace::take();
        assert_eq!(actual.len(),1);
        assert_eq!(actual[0],(tag,index,E::ZERO.to_le_bytes()));
        assert!(crate::trace::take().is_empty());
    }
}

#[cfg(kani)]
mod tls_programmed23 {
    use super::*;
    type Store = RefCell<Option<(Table,BTreeSet<Vec<u8>>)>>;
    static mut SLOT: Store = RefCell::new(None);
    // Concrete instantiation for PROGRAMMED only; this gate calls no trace
    // or timing TLS. Same single-thread live-key contract as the trace gate.
    fn single_with<T:'static,F,R>(_: &std::thread::LocalKey<T>, f:F)->R
    where F:FnOnce(&T)->R {
        unsafe { f(&*(core::ptr::addr_of!(SLOT) as *const T)) }
    }
    #[kani::proof]
    #[kani::unwind(4)]
    #[kani::stub(std::thread::LocalKey::with,single_with)]
    fn install_uninstall_empty() {
        assert_eq!(uninstall(),(0,0));
        install(Table::new());
        unsafe { assert!((&*core::ptr::addr_of!(SLOT)).borrow().is_some()); }
        assert_eq!(uninstall(),(0,0));
        unsafe { assert!((&*core::ptr::addr_of!(SLOT)).borrow().is_none()); }
        assert_eq!(uninstall(),(0,0));
    }
}

#[cfg(kani)]
mod tls22 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(34)]
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

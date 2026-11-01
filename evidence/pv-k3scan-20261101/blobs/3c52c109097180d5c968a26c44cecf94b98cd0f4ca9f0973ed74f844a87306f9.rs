#[cfg(kani)]
mod proofs {
    #[kani::proof]
    #[kani::unwind(66)]
    fn zeroizing_new_as_mut64_source_values() {
        let original: [u8; 64] = kani::any();
        let mut wrapped = zeroize::Zeroizing::new(original);
        assert!(*wrapped == original);
        let index: usize = kani::any();
        kani::assume(index < 64);
        let replacement: u8 = kani::any();
        {
            let borrowed: &mut [u8] = wrapped.as_mut();
            assert!(borrowed.len() == 64);
            assert!(borrowed[index] == original[index]);
            borrowed[index] = replacement;
        }
        assert!(wrapped[index] == replacement);
        drop(wrapped);
    }
}

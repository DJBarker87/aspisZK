include!("selected.rs");
#[cfg(kani)]
mod pv6 {
    use super::*;
    #[kani::proof] #[kani::unwind(34)]
    fn zeroizing_zero32_source() {
        let a = Zeroizing::new([0u8;32]);
        assert!(*a == [0;32]);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn zeroizing_zero64_source() {
        let a = Zeroizing::new([0u8;64]);
        assert!(*a == [0;64]);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split64_values_source() {
        let a: [u8;64] = kani::any();
        let bytes = Zeroizing::new(a);
        let mut field = Zeroizing::new([0u8;32]);
        let mut salt = Zeroizing::new([0u8;32]);
        field.copy_from_slice(&bytes[..32]);
        salt.copy_from_slice(&bytes[32..]);
        let i: usize = kani::any(); kani::assume(i<32);
        assert!(field[i] == a[i]); assert!(salt[i] == a[i+32]);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split64_halves_independent() {
        let a: [u8;32] = kani::any(); let b: [u8;32] = kani::any();
        let mut bytes = Zeroizing::new([0u8;64]);
        bytes[..32].copy_from_slice(&a); bytes[32..].copy_from_slice(&b);
        let mut field = Zeroizing::new([0u8;32]); let mut salt = Zeroizing::new([0u8;32]);
        field.copy_from_slice(&bytes[..32]); salt.copy_from_slice(&bytes[32..]);
        assert!(*field==a); assert!(*salt==b);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split64_nonzero_gate_source() {
        let a: [u8;64] = kani::any(); let bytes = Zeroizing::new(a);
        let mut field = Zeroizing::new([0u8;32]); let mut salt = Zeroizing::new([0u8;32]);
        field.copy_from_slice(&bytes[..32]); salt.copy_from_slice(&bytes[32..]);
        assert_eq!(entropy_nonzero32(&field) && entropy_nonzero32(&salt),
            *field != [0;32] && *salt != [0;32]);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split64_guard_rejects_zero_field() {
        let salt: [u8;32] = kani::any(); let mut bytes = Zeroizing::new([0u8;64]);
        bytes[32..].copy_from_slice(&salt);
        let mut field = Zeroizing::new([0u8;32]); field.copy_from_slice(&bytes[..32]);
        assert!(!entropy_nonzero32(&field));
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split64_guard_rejects_zero_salt() {
        let field: [u8;32] = kani::any(); let mut bytes = Zeroizing::new([0u8;64]);
        bytes[..32].copy_from_slice(&field);
        let mut salt = Zeroizing::new([0u8;32]); salt.copy_from_slice(&bytes[32..]);
        assert!(!entropy_nonzero32(&salt));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn zeroizing_slice_back32() {
        let a: [u8;32] = kani::any(); let mut value = Zeroizing::new(a);
        let i: usize = kani::any(); kani::assume(i<32); let byte: u8 = kani::any();
        let slice: &mut [u8] = value.as_mut(); slice[i] = byte;
        assert!(value[i] == byte);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn zeroizing_lower_slice_back64() {
        let a: [u8;64] = kani::any(); let mut value = Zeroizing::new(a);
        let b: [u8;32] = kani::any(); value[..32].copy_from_slice(&b);
        let i: usize = kani::any(); kani::assume(i<32);
        assert!(value[i]==b[i]); assert!(value[i+32]==a[i+32]);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn zeroizing_upper_slice_back64() {
        let a: [u8;64] = kani::any(); let mut value = Zeroizing::new(a);
        let b: [u8;32] = kani::any(); value[32..].copy_from_slice(&b);
        let i: usize = kani::any(); kani::assume(i<32);
        assert!(value[i]==a[i]); assert!(value[i+32]==b[i]);
    }
    #[kani::proof] #[kani::unwind(67)]
    fn native_factory_preserves_nonce() {
        let nonce: [u8;32] = kani::any(); kani::assume(entropy_nonzero32(&nonce));
        if let Ok(secrets) = StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            assert!(secrets.mask_nonce==nonce);
        }
    }
}

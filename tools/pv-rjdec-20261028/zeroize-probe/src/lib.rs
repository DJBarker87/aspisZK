use zeroize::Zeroize;

#[unsafe(no_mangle)]
#[inline(never)]
pub fn rjdec_zeroize_byte(byte: &mut u8) {
    byte.zeroize();
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn rjdec_zeroize_array(bytes: &mut [u8; 32]) {
    bytes.zeroize();
}

// Source form used by the retained compiler-fence model. This is a control,
// never substituted for the reached zeroize 1.9.0 implementation above.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn rjdec_legacy_byte_control(byte: &mut u8) {
    unsafe { core::ptr::write_volatile(byte, 0) };
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

#[test]
fn values_agree_while_effect_primitives_differ() {
    for value in 0..=255 {
        let mut actual = value;
        let mut legacy = value;
        rjdec_zeroize_byte(&mut actual);
        rjdec_legacy_byte_control(&mut legacy);
        assert_eq!((actual, legacy), (0, 0));
        let mut bytes = [value; 32];
        rjdec_zeroize_array(&mut bytes);
        assert_eq!(bytes, [0; 32]);
    }
}

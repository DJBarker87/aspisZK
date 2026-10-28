use aspis_core::field::{M31, CM31, QM31};
use std::ptr::NonNull;
const _: () = assert!(size_of::<M31>() == 4 && align_of::<M31>() == 4);
const _: () = assert!(size_of::<QM31>() == 16 && align_of::<QM31>() == 4);
fn main() {
    let xs: [QM31; 1024] = std::array::from_fn(|i| QM31 {
        c0: CM31 { a: M31((i as u32).wrapping_mul(0xffffffff)), b: M31(0x80000000 ^ i as u32) },
        c1: CM31 { a: M31(i as u32), b: M31(!(i as u32)) },
    });
    let before = xs;
    let ptr = NonNull::from_ref(&xs[..]).cast::<QM31>();
    let end = unsafe { ptr.add(xs.len()) };
    assert_eq!(unsafe { end.offset_from_unsigned(ptr) }, 1024);
    let mut indexed = QM31::ZERO;
    for i in 0..xs.len() {
        let word = unsafe { ptr.add(i).as_ptr().read() };
        assert_eq!(word, xs[i]);
        indexed = indexed.add(word);
    }
    let folded = xs.iter().copied().fold(QM31::ZERO, QM31::add);
    assert_eq!(folded, indexed);
    assert_eq!(xs, before);
    println!("PASS M31 size4 align4; QM31 size16 align4; 1024 raw-word shared pointer reads; offset length; copied fold and complete backing storage match. Finite validation only.");
}

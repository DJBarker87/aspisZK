pub mod field {
#[derive(Clone,Copy)] pub struct M31(pub u32);
#[derive(Clone,Copy)] pub struct CM31 { pub a:M31,pub b:M31 }
#[derive(Clone,Copy)] pub struct QM31 { pub c0:CM31,pub c1:CM31 }
#[derive(Clone,Copy)] pub struct WideExact { c0:QM31,c1:QM31 }
}
pub mod sampler { use crate::field::WideExact;
fn low_base_p_digits(_: &[u8;32])->([u32;8],u32) {unreachable!()}
fn add_small_base_p(_: &mut [u32;8],_:u32)->bool {unreachable!()}
fn decode8(_: [u32;8])->WideExact {unreachable!()}
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}
}

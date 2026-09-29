// Multiplication by 2^-n is a rotation of a canonical 31-bit word. The
// canonical guard is explicit; raw constructors keep the original M31 mul.
#[inline(always)]
pub fn scale_power_of_two(value:K,n:usize)->K {
    assert!(n<=10);
    let limbs=[value.c0.a.0,value.c0.b.0,value.c1.a.0,value.c1.b.0];
    if limbs.iter().all(|&v|v<P) {
        let rot=|x:u32|M31(((x>>n)|(x<<(31-n)))&P);
        K{c0:aspis_core::field::CM31::new(rot(limbs[0]),rot(limbs[1])),
          c1:aspis_core::field::CM31::new(rot(limbs[2]),rot(limbs[3]))}
    } else {
        value.mul_m31(if n==0 {M31::ONE}else{M31(1u32<<(31-n))})
    }
}

// Owned reference and unrestricted-carrier P6 check; appended inside wide_exact.rs.
#[cfg(kani)]
mod pv_cb3_arbitrary_bytes {
    use super::*;
pub fn wide_bytes_flat(x:crate::field::WideExact)->[u8;32] {
 let l=x.to_limbs();let a=l[0].to_le_bytes();let b=l[1].to_le_bytes();let c=l[2].to_le_bytes();let d=l[3].to_le_bytes();
 let e=l[4].to_le_bytes();let f=l[5].to_le_bytes();let g=l[6].to_le_bytes();let h=l[7].to_le_bytes();
 [a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]
}
    #[kani::proof]
    #[kani::unwind(33)]
    fn all_carriers() {
        let w: [u32; 8] = kani::any();
        let x = WideExact {
            c0: QM31 { c0: CM31 { a:M31(w[0]), b:M31(w[1]) }, c1: CM31 { a:M31(w[2]), b:M31(w[3]) } },
            c1: QM31 { c0: CM31 { a:M31(w[4]), b:M31(w[5]) }, c1: CM31 { a:M31(w[6]), b:M31(w[7]) } },
        };
        assert_eq!(x.to_le_bytes(), wide_bytes_flat(x));
    }
}

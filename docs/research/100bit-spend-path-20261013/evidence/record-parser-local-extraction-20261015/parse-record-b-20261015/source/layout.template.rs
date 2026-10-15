#![no_std]
#![allow(dead_code)]
extern crate self as aspis_core;
pub mod field {
    include!("fragments/modulus.rs");
    include!("fragments/m31.rs");
    include!("fragments/cm31.rs");
    include!("fragments/qm31.rs");
    impl QM31 {
        include!("fragments/qm31_zero.rs");
    }
    mod wide_exact {
        use super::{CM31, M31, P, QM31};
        include!("fragments/wide_type.rs");
        impl WideExact {
            include!("fragments/wide_limb_count.rs");
            include!("fragments/wide_byte_len.rs");
            include!("fragments/wide_c1.rs");
            include!("fragments/wide_from_limbs.rs");
            include!("fragments/wide_from_le_bytes.rs");
        }
    }
    pub use wide_exact::WideExact;
}
pub mod r1_wire {
    use aspis_core::field::{QM31, WideExact};
    include!("fragments/lanes.rs");
    include!("fragments/points.rs");
    include!("fragments/claims.rs");
    include!("fragments/wire_error.rs");
    include!("fragments/row_shape.rs");
    include!("fragments/parse_record.rs");
}

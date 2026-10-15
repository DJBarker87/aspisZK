// Namespace-only extraction layout. Every recorded declaration is inserted verbatim.
#![no_std]
#![allow(dead_code)]
pub mod aspis_core {
    pub mod field {
        include!("fragments/m31_modulus.rs");
        include!("fragments/m31_type.rs");
    }
}
pub mod poseidon2 {
    use crate::aspis_core::field::M31;
    include!("fragments/digest_elems.rs");
    include!("fragments/digest_alias.rs");
}
include!("fragments/value_limit.rs");
pub mod pool_v1 {
    include!("fragments/pool_tree_depth.rs");
    include!("fragments/leaf_capacity.rs");
    pub mod payment_relation {
        use crate::aspis_core::field::{M31, P};
        use crate::{poseidon2::Digest, VALUE_LIMIT};
        use super::POOL_V1_LEAF_CAPACITY;
        include!("fragments/withdrawal_public_type.rs");
        include!("fragments/payment_error.rs");
        include!("fragments/common_public.rs");
        include!("fragments/digest_is_canonical.rs");
        include!("fragments/validate_common.rs");
        include!("fragments/withdrawal_common.rs");
        include!("fragments/validate_withdrawal.rs");
    }
}

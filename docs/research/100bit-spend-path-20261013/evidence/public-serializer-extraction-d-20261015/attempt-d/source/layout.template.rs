// Source-preserving module layout for extraction-tool input review.
// Every declaration body is included unchanged from its recorded fragment.
// This layout is not compiled as part of kit generation.
extern crate alloc;

pub mod aspis_core {
    pub mod field {
        include!("fragments/m31_modulus.rs");
        include!("fragments/m31_type.rs");
    }
    pub mod state_only_prefix {
        #[cfg(feature = "r0")]
        pub mod r0 {
            include!("fragments/r0_error.rs");
        }
    }
}

pub mod poseidon2 {
    use crate::aspis_core::field::M31;
    include!("fragments/digest_elems.rs");
    include!("fragments/digest_alias.rs");
}

pub mod pool_v1 {
    pub mod format {
        include!("fragments/pool_tree_depth.rs");
    }
    pub use format::POOL_V1_TREE_DEPTH;

    pub mod pair_terminal {
        use crate::poseidon2::Digest;
        include!("fragments/verified_afterstate.rs");
    }
    pub use pair_terminal::PoolV1PairVerifiedAfterstateV1;

    pub mod pair_tree_profile {
        use crate::poseidon2::Digest;
        use super::{PoolV1PairVerifiedAfterstateV1, POOL_V1_TREE_DEPTH};
        include!("fragments/pair_tree_depth.rs");
        include!("fragments/live_snapshot.rs");
        include!("fragments/late_public_statement.rs");
    }
    pub use pair_tree_profile::POOL_V1_PAIR_TREE_DEPTH;

    pub mod payment_relation {
        use crate::aspis_core::field::M31;
        use crate::poseidon2::Digest;
        include!("fragments/transfer_public.rs");
        include!("fragments/withdrawal_public_type.rs");
    }

    pub mod pair_forest_semantic_terminal {
        use crate::aspis_core::field::M31;
        use crate::poseidon2::Digest;
        use super::{
            pair_tree_profile::PoolV1PairLatePublicStatementV1,
            payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
        };

        include!("fragments/compiled_variant.rs");
        include!("fragments/semantic_public.rs");
        include!("fragments/private_public.rs");
        include!("fragments/withdrawal_public.rs");

        #[cfg(feature = "r0")]
        pub mod r0 {
            use alloc::vec::Vec;
            use crate::aspis_core;
            use crate::aspis_core::{field::{M31, P}, state_only_prefix::r0::Error};
            use super::*;
            include!("fragments/r0_public_enum.rs");
            impl<'a> Public<'a> {
                include!("fragments/r0_public_semantic_method.rs");
                include!("fragments/public_bytes_method.rs");
            }
        }
    }
}

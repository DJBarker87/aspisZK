// Source-preserving module layout for extraction-tool input review.
// Every declaration body is included unchanged from its recorded fragment.
// This layout is not compiled as part of kit generation.
extern crate alloc;

pub mod aspis_core {
    include!("fragments/digest_trait.rs");
    pub mod field {
        include!("fragments/cm31_type.rs");
        include!("fragments/qm31_type.rs");
        impl CM31 {
            include!("fragments/cm31_new.rs");
        }
        impl QM31 {
            include!("fragments/qm31_zero.rs");
        }
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

    pub mod pair_forest_terminal {
        use crate::poseidon2::Digest;
        use super::pair_tree_profile::PoolV1PairLatePublicStatementV1;
        use super::payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1};
        include!("fragments/terminal_common.rs");
        include!("fragments/terminal_statement.rs");
        impl PoolV1PairForestTerminalStatementV1 {
            include!("fragments/semantic_public_method.rs");
        }
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

pub mod sampler {
 use crate::aspis_core::field::{CM31,M31,P,QM31};
 include!("fragments/qm31_div_pass.rs");
 include!("fragments/qm31_digits.rs");
 include!("fragments/qm31_sample.rs");
}
pub mod r1_wire {
 use crate::aspis_core::field::QM31;
 use crate::sampler::qm31_sample;
 include!("fragments/challenges.rs");
 include!("fragments/validated_type.rs");
 impl<'a> ValidatedRecord<'a> {
 include!("fragments/validated_row.rs");
 include!("fragments/validated_framed.rs");
 }
 include!("fragments/prefix_type.rs");
 impl<'a> Prefix<'a> {
 include!("fragments/prefix_record.rs");
 include!("fragments/prefix_validated_record.rs");
 }
 include!("fragments/begin.rs");
    use crate::aspis_core::Digest32;
    include!("fragments/wire_error.rs");
    include!("fragments/domain_plain.rs");
    include!("fragments/domain_salted.rs");
    include!("fragments/transcript_type.rs");
    impl<H: Digest32> SemanticTranscript<H> {
        include!("fragments/transcript_new.rs");
        include!("fragments/transcript_step.rs");
        include!("fragments/semantic_validated.rs");
    }
    pub fn semantic_validated_entry<H: Digest32>(transcript: &mut SemanticTranscript<H>, record: ValidatedRecord<'_>) -> Result<QM31, Error> { transcript.semantic_validated(record) }
    pub fn prefix_validated_entry<'a>(prefix: &Prefix<'a>, row: u8) -> Result<ValidatedRecord<'a>, Error> { prefix.validated_record(row) }
    // Extraction-only entry wrapper: actual private method body is unchanged.
    pub fn sample_validated_entry<H: Digest32>(
        transcript: &mut SemanticTranscript<H>, row: u8, framed: &[u8],
    ) -> Result<[u8; 32], Error> {
        transcript.sample_block_validated(row, framed)
    }
}

pub mod r1_semantic {
    use crate::aspis_core::Digest32;
    use crate::r1_wire::{Error, SemanticTranscript};
    use crate::pool_v1::pair_forest_semantic_terminal::r0::Public;
    include!("fragments/public_transcript.rs");
}

pub mod transport {
 include!("fragments/variant.rs");
 impl Variant {
 include!("fragments/variant_tag.rs");
 }
}
pub mod transcript {
 use crate::aspis_core::Digest32;
 use crate::transport::Variant;
 include!("fragments/opening_type.rs");
 impl<H: Digest32> Transcript<H> {
 include!("fragments/opening_new.rs");
 include!("fragments/opening_absorb.rs");
 include!("fragments/opening_block.rs");
 }
}

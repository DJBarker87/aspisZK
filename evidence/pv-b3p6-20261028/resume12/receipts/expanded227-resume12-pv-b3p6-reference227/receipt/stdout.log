#![feature(prelude_import)]
//! Owned byte-identical deployed host terminal. No reference law is claimed yet.
extern crate std;
#[prelude_import]
use std::prelude::rust_2021::*;
extern crate alloc;
mod host_terminal_field {





    //! Gated terminal arithmetic helpers; same field operation and accumulation order.
    use aspis_core::field::{M31, CM31, QM31, P};
    #[inline(always)]
    fn cm31_mul_r(value: CM31) -> CM31 {
        CM31::new(value.a.double().sub(value.b),
            value.a.add(value.b.double()))
    }
    pub(crate) struct PreparedQm31Multiplier {
        components: [[M31; 3]; 3],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for PreparedQm31Multiplier { }
    #[automatically_derived]
    impl ::core::clone::Clone for PreparedQm31Multiplier {
        #[inline]
        fn clone(&self) -> PreparedQm31Multiplier {
            let _: ::core::clone::AssertParamIsClone<[[M31; 3]; 3]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PreparedQm31Multiplier { }
    #[inline(always)]
    fn prepare_component(component: CM31) -> [M31; 3] {
        [component.a, component.b, component.a.add(component.b)]
    }
    #[inline(always)]
    fn prepared_component_mul(left: [M31; 3], right: CM31) -> CM31 {
        let m0 = left[0].mul(right.a);
        let m1 = left[1].mul(right.b);
        let m2 = left[2].mul(right.a.add(right.b));
        CM31 { a: m0.sub(m1), b: m2.sub(m0).sub(m1) }
    }
    impl PreparedQm31Multiplier {
        #[inline(always)]
        pub(crate) fn new(value: QM31) -> Self {
            Self {
                components: [prepare_component(value.c0),
                        prepare_component(value.c1),
                        prepare_component(value.c0.add(value.c1))],
            }
        }
        #[inline(always)]
        pub(crate) fn mul(self, rhs: QM31) -> QM31 {
            let m0 = prepared_component_mul(self.components[0], rhs.c0);
            let m1 = prepared_component_mul(self.components[1], rhs.c1);
            let m2 =
                prepared_component_mul(self.components[2],
                    rhs.c0.add(rhs.c1));
            QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
        }
    }
    #[inline(always)]
    fn reconstruct_component(channels: [u64; 3]) -> CM31 {
        let m0 = M31::reduce_u64(channels[0]);
        let m1 = M31::reduce_u64(channels[1]);
        let m2 = M31::reduce_u64(channels[2]);
        CM31 { a: m0.sub(m1), b: m2.sub(m0).sub(m1) }
    }
    #[inline(always)]
    fn reconstruct_channels(sums: [[u64; 3]; 3]) -> QM31 {
        let m0 = reconstruct_component(sums[0]);
        let m1 = reconstruct_component(sums[1]);
        let m2 = reconstruct_component(sums[2]);
        QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
    }
    #[inline(always)]
    fn accumulate_channels(mut sums: [[u64; 3]; 3], left: QM31, right: QM31)
        -> [[u64; 3]; 3] {
        let left_sum = left.c0.add(left.c1);
        let right_sum = right.c0.add(right.c1);
        let a =
            [[left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
                    [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
                    [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)]];
        let b =
            [[right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
                    [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
                    [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)]];
        sums[0][0] += a[0][0].0 as u64 * b[0][0].0 as u64;
        sums[0][1] += a[0][1].0 as u64 * b[0][1].0 as u64;
        sums[0][2] += a[0][2].0 as u64 * b[0][2].0 as u64;
        sums[1][0] += a[1][0].0 as u64 * b[1][0].0 as u64;
        sums[1][1] += a[1][1].0 as u64 * b[1][1].0 as u64;
        sums[1][2] += a[1][2].0 as u64 * b[1][2].0 as u64;
        sums[2][0] += a[2][0].0 as u64 * b[2][0].0 as u64;
        sums[2][1] += a[2][1].0 as u64 * b[2][1].0 as u64;
        sums[2][2] += a[2][2].0 as u64 * b[2][2].0 as u64;
        sums
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products2(left: [QM31; 2], right: [QM31; 2])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products3(left: [QM31; 3], right: [QM31; 3])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        let sums = accumulate_channels(sums, left[2], right[2]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products4(left: [QM31; 4], right: [QM31; 4])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        let sums = accumulate_channels(sums, left[2], right[2]);
        let sums = accumulate_channels(sums, left[3], right[3]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    fn terminal_limb(value: M31) -> u64 { u64::from(value.0) }
    #[inline(always)]
    pub(crate) fn qm31_pack_base4(values: &[QM31]) -> QM31 {
        if !(values.len() <= 4) {
            ::core::panicking::panic("assertion failed: values.len() <= 4")
        };
        let mut padded = [QM31::ZERO; 4];
        let mut i = 0usize;
        while i < values.len() { padded[i] = values[i]; i += 1; }
        let [v0, v1, v2, v3] = padded;
        let p = u64::from(P);
        let c0_a =
            terminal_limb(v0.c0.a) + (p - terminal_limb(v1.c0.b)) +
                            2 * terminal_limb(v2.c1.a) + (p - terminal_limb(v2.c1.b)) +
                    (p - terminal_limb(v3.c1.a)) +
                (2 * p - 2 * terminal_limb(v3.c1.b));
        let c0_b =
            terminal_limb(v0.c0.b) + terminal_limb(v1.c0.a) +
                            terminal_limb(v2.c1.a) + 2 * terminal_limb(v2.c1.b) +
                    2 * terminal_limb(v3.c1.a) + (p - terminal_limb(v3.c1.b));
        let c1_a =
            terminal_limb(v0.c1.a) + (p - terminal_limb(v1.c1.b)) +
                    terminal_limb(v2.c0.a) + (p - terminal_limb(v3.c0.b));
        let c1_b =
            terminal_limb(v0.c1.b) + terminal_limb(v1.c1.a) +
                    terminal_limb(v2.c0.b) + terminal_limb(v3.c0.a);
        QM31 {
            c0: CM31::new(M31::reduce_u64(c0_a), M31::reduce_u64(c0_b)),
            c1: CM31::new(M31::reduce_u64(c1_a), M31::reduce_u64(c1_b)),
        }
    }
}
mod host_copy_terminal {
    //! Allocation-bounded SBF-safe Copy lane for the eight-lane Pool V1
    //! pair-forest relation.
    //!
    //! Runtime evaluation consumes only generated patterns, endpoints and fixed
    //! active-row masks. The allocation-heavy typed registry remains the
    //! independent host compiler/reference boundary and is not linked on SBF.
    macro_rules! qm31_array {
        ($n:expr, $index:ident, $body:expr) =>
        {{
                let mut output = [QM31::ZERO; $n]; let mut $index = 0usize;
                while $index < $n { output[$index] = $body; $index += 1; }
                output
            }};
    }
    use crate::host_terminal_field::PreparedQm31Multiplier;
    use aspis_core::field::{CM31, M31, QM31};
    use aspis_statement::poseidon2::POSEIDON2_WIDTH;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1: usize = 1024;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1: usize = 16;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1: usize = 136;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1: usize = 14;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1:
        usize =
        if false { 2 } else { 1 };
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize
        =
        core::mem::size_of::<Selectors>();
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1: usize =
        if false { 103 * core::mem::size_of::<QM31>() } else { 0 };
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_BYTES_V1: usize =
        POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1 +
            POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1;
    pub const
        PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1:
        u64 =
        constants::ACTIVE_ROWS_FINGERPRINT;
    /// Exact SBF-safe active-row schedule consumed by the selected verifier.
    /// Host generation tests independently replay it from the typed tuple registry.
    pub fn pool_v1_pair_forest_copy_active_row_masks_compiled_v1()
        -> &'static [u16; 64] {
        &constants::ACTIVE_ROW_MASKS
    }
    /// Frozen row-to-group schedule generated from the exact pair-forest copy
    /// registry.  The selected verifier consumes this directly instead of
    /// rebuilding and deduplicating public layout data on every transaction.
    pub fn pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1()
        -> &'static [u8; 64] {
        &constants::INACTIVE_ROW_GROUPS
    }
    /// Deduplicated inactive masks referenced by
    /// [`pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1`].
    pub fn pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()
        -> &'static [u16] {
        &constants::INACTIVE_GROUP_MASKS
    }
    const _: () =
        if !(POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1)
            {
            ::core::panicking::panic("assertion failed: POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1")
        };
    const _: () =
        if !(constants::COPY_LINKS.len() ==
                    POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1) {
            ::core::panicking::panic("assertion failed: constants::COPY_LINKS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1")
        };
    const _: () =
        if !(constants::COPY_PATTERNS.len() ==
                    POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1) {
            ::core::panicking::panic("assertion failed: constants::COPY_PATTERNS.len() ==\n    POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1")
        };
    const _: () =
        if !(constants::ACTIVE_ROW_MASKS.len() == 64) {
            ::core::panicking::panic("assertion failed: constants::ACTIVE_ROW_MASKS.len() == 64")
        };
    const _: () =
        if !(constants::INACTIVE_ROW_GROUPS.len() == 64) {
            ::core::panicking::panic("assertion failed: constants::INACTIVE_ROW_GROUPS.len() == 64")
        };
    const _: () =
        if !(constants::INACTIVE_GROUP_MASKS.len() <= 64) {
            ::core::panicking::panic("assertion failed: constants::INACTIVE_GROUP_MASKS.len() <= 64")
        };
    pub enum PoolV1PairForestCompiledVariantV1 {
        PrivateTransfer,
        Withdrawal,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestCompiledVariantV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestCompiledVariantV1 { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestCompiledVariantV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    PoolV1PairForestCompiledVariantV1::PrivateTransfer =>
                        "PrivateTransfer",
                    PoolV1PairForestCompiledVariantV1::Withdrawal =>
                        "Withdrawal",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestCompiledVariantV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestCompiledVariantV1) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub struct PoolV1PairForestCompiledCopyTerminalV1 {
        pub residual: QM31,
        pub active: QM31,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestCompiledCopyTerminalV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestCompiledCopyTerminalV1 {
            let _: ::core::clone::AssertParamIsClone<QM31>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestCompiledCopyTerminalV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(f,
                "PoolV1PairForestCompiledCopyTerminalV1", "residual",
                &self.residual, "active", &&self.active)
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestCompiledCopyTerminalV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestCompiledCopyTerminalV1) -> bool {
            self.residual == other.residual && self.active == other.active
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<QM31>;
        }
    }
    struct CompiledPoolV1PairForestPattern {
        /// 0 = zero, 1 = row-local C1 cell plus a canonical M31 offset.
        kinds: [u8; POSEIDON2_WIDTH],
        columns: [u8; POSEIDON2_WIDTH],
        offsets: [u32; POSEIDON2_WIDTH],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        CompiledPoolV1PairForestPattern {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestPattern {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestPattern {
            let _: ::core::clone::AssertParamIsClone<[u8; POSEIDON2_WIDTH]>;
            let _: ::core::clone::AssertParamIsClone<[u8; POSEIDON2_WIDTH]>;
            let _: ::core::clone::AssertParamIsClone<[u32; POSEIDON2_WIDTH]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestPattern { }
    struct CompiledPoolV1PairForestEndpoint {
        row: u16,
        slot: u8,
        pattern: u8,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        CompiledPoolV1PairForestEndpoint {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestEndpoint {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestEndpoint {
            let _: ::core::clone::AssertParamIsClone<u16>;
            let _: ::core::clone::AssertParamIsClone<u8>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestEndpoint { }
    struct CompiledPoolV1PairForestLink {
        tag: u32,
        /// 0 = one, 1 = transfer, 2 = withdrawal, 3 = append-left,
        /// 4 = append-right.
        weight_kind: u8,
        weight_level: u8,
        producer: CompiledPoolV1PairForestEndpoint,
        consumer: CompiledPoolV1PairForestEndpoint,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CompiledPoolV1PairForestLink {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestLink {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestLink {
            let _: ::core::clone::AssertParamIsClone<u32>;
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _:
                    ::core::clone::AssertParamIsClone<CompiledPoolV1PairForestEndpoint>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestLink { }
    mod constants {
        use super::{
            CompiledPoolV1PairForestEndpoint, CompiledPoolV1PairForestLink,
            CompiledPoolV1PairForestPattern,
        };
        pub(crate) const ACTIVE_ROWS_FINGERPRINT: u64 = 0xdf394a5a8554d09c;
        pub(crate) const ACTIVE_ROW_MASKS: [u16; 64] =
            [6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048,
                    6145, 2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214,
                    26214, 26214, 26214, 1749];
        pub(crate) const INACTIVE_ROW_GROUPS: [u8; 64] =
            [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                    1, 1, 1, 0, 2, 3, 1, 4, 3, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 5, 5, 5,
                    5, 6];
        pub(crate) const INACTIVE_GROUP_MASKS: [u16; 7] =
            [59391, 59390, 61438, 63487, 63486, 39321, 63786];
        pub(crate) const COPY_PATTERNS: [CompiledPoolV1PairForestPattern; 14]
            =
            [CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                        columns: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                                15],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0,
                                0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 1051521018, 0, 0, 0, 0, 0, 0,
                                0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0,
                                0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    }];
        pub(crate) const COPY_LINKS: [CompiledPoolV1PairForestLink; 136] =
            [CompiledPoolV1PairForestLink {
                        tag: 1124073472,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 27,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 32,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073473,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 43,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 48,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073474,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 411,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 416,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073475,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 443,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 448,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073476,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 459,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 464,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073477,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 491,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 496,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073478,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 507,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 512,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073479,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 11,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 28,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073480,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 12,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 412,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073481,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 44,
                            slot: 0,
                            pattern: 2,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 428,
                            slot: 0,
                            pattern: 3,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073482,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 60,
                            slot: 0,
                            pattern: 4,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 428,
                            slot: 1,
                            pattern: 5,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073483,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 44,
                            slot: 1,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1008,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073484,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 460,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1010,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073485,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 508,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1012,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073486,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1008,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 0,
                            pattern: 6,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073487,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1010,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 1,
                            pattern: 8,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073488,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1012,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1015,
                            slot: 0,
                            pattern: 8,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073489,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 0,
                            pattern: 9,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1015,
                            slot: 1,
                            pattern: 6,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073490,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 64,
                            slot: 0,
                            pattern: 10,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1017,
                            slot: 0,
                            pattern: 11,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073491,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 913,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1017,
                            slot: 1,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073492,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 523,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1018,
                            slot: 0,
                            pattern: 11,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073493,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 475,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 540,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073494,
                        weight_kind: 2,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 523,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 540,
                            slot: 1,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073495,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1018,
                            slot: 0,
                            pattern: 11,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 528,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073496,
                        weight_kind: 3,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 539,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 556,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073497,
                        weight_kind: 4,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 539,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 544,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073498,
                        weight_kind: 3,
                        weight_level: 1,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 555,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 572,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073499,
                        weight_kind: 4,
                        weight_level: 1,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 555,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 560,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073500,
                        weight_kind: 3,
                        weight_level: 2,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 571,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 588,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073501,
                        weight_kind: 4,
                        weight_level: 2,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 571,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 576,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073502,
                        weight_kind: 3,
                        weight_level: 3,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 587,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 604,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073503,
                        weight_kind: 4,
                        weight_level: 3,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 587,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 592,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073504,
                        weight_kind: 3,
                        weight_level: 4,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 603,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 620,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073505,
                        weight_kind: 4,
                        weight_level: 4,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 603,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 608,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073506,
                        weight_kind: 3,
                        weight_level: 5,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 619,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 636,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073507,
                        weight_kind: 4,
                        weight_level: 5,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 619,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 624,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073508,
                        weight_kind: 3,
                        weight_level: 6,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 635,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 652,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073509,
                        weight_kind: 4,
                        weight_level: 6,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 635,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 640,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073510,
                        weight_kind: 3,
                        weight_level: 7,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 651,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 668,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073511,
                        weight_kind: 4,
                        weight_level: 7,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 651,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 656,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073512,
                        weight_kind: 3,
                        weight_level: 8,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 667,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 684,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073513,
                        weight_kind: 4,
                        weight_level: 8,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 667,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 672,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073514,
                        weight_kind: 3,
                        weight_level: 9,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 683,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 700,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073515,
                        weight_kind: 4,
                        weight_level: 9,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 683,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 688,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073516,
                        weight_kind: 3,
                        weight_level: 10,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 699,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 716,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073517,
                        weight_kind: 4,
                        weight_level: 10,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 699,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 704,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073518,
                        weight_kind: 3,
                        weight_level: 11,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 715,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 732,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073519,
                        weight_kind: 4,
                        weight_level: 11,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 715,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 720,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073520,
                        weight_kind: 3,
                        weight_level: 12,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 731,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 748,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073521,
                        weight_kind: 4,
                        weight_level: 12,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 731,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 736,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073522,
                        weight_kind: 3,
                        weight_level: 13,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 747,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 764,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073523,
                        weight_kind: 4,
                        weight_level: 13,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 747,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 752,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073524,
                        weight_kind: 3,
                        weight_level: 14,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 763,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 780,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073525,
                        weight_kind: 4,
                        weight_level: 14,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 763,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 768,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073526,
                        weight_kind: 3,
                        weight_level: 15,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 779,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 796,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073527,
                        weight_kind: 4,
                        weight_level: 15,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 779,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 784,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073528,
                        weight_kind: 3,
                        weight_level: 16,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 795,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 812,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073529,
                        weight_kind: 4,
                        weight_level: 16,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 795,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 800,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073530,
                        weight_kind: 3,
                        weight_level: 17,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 811,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 828,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073531,
                        weight_kind: 4,
                        weight_level: 17,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 811,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 816,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073532,
                        weight_kind: 3,
                        weight_level: 18,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 827,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 844,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073533,
                        weight_kind: 4,
                        weight_level: 18,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 827,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 832,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073534,
                        weight_kind: 3,
                        weight_level: 19,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 843,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 860,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073535,
                        weight_kind: 4,
                        weight_level: 19,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 843,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 848,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073536,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 59,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 913,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073537,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 914,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 76,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073538,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 914,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 64,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073539,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 75,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 917,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073540,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 918,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 92,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073541,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 918,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 80,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073542,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 91,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 921,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073543,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 922,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 108,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073544,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 922,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 96,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073545,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 107,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 925,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073546,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 926,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 124,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073547,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 926,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 112,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073548,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 123,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 929,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073549,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 930,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 140,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073550,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 930,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 128,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073551,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 139,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 933,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073552,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 934,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 156,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073553,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 934,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 144,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073554,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 155,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 937,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073555,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 938,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 172,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073556,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 938,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 160,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073557,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 171,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 941,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073558,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 942,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 188,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073559,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 942,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 176,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073560,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 187,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 945,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073561,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 946,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 204,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073562,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 946,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 192,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073563,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 203,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 949,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073564,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 950,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 220,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073565,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 950,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 208,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073566,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 219,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 953,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073567,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 954,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 236,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073568,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 954,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 224,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073569,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 235,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 957,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073570,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 958,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 252,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073571,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 958,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 240,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073572,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 251,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 961,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073573,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 962,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 268,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073574,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 962,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 256,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073575,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 267,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 965,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073576,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 966,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 284,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073577,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 966,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 272,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073578,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 283,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 969,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073579,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 970,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 300,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073580,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 970,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 288,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073581,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 299,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 973,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073582,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 974,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 316,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073583,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 974,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 304,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073584,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 315,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 977,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073585,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 978,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 332,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073586,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 978,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 320,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073587,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 331,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 981,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073588,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 982,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 348,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073589,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 982,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 336,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073590,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 347,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 985,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073591,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 986,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 364,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073592,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 986,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 352,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073593,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 363,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 989,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073594,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 990,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 380,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073595,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 990,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 368,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073596,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 379,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 993,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073597,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 994,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 396,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073598,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 994,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 384,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073599,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 395,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 997,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073600,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 998,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 876,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073601,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 998,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 864,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073602,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 875,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1001,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073603,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1002,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 892,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073604,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1002,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 880,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073605,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 891,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1005,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073606,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1006,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 908,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073607,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1006,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 896,
                            slot: 0,
                            pattern: 10,
                        },
                    }];
    }
    #[inline(always)]
    fn lift_m31(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    #[inline(always)]
    fn selector_mask_sum_16(values: &[QM31; 16], mut mask: u16) -> QM31 {
        let complement = mask.count_ones() > 8;
        if complement { mask = !mask; }
        let mut sum = if complement { QM31::ONE } else { QM31::ZERO };
        while mask != 0 {
            let index = mask.trailing_zeros() as usize;
            sum =
                if complement {
                    sum.sub(values[index])
                } else { sum.add(values[index]) };
            mask &= mask - 1;
        }
        sum
    }
    pub(crate) struct Selectors {
        pub(crate) high: [QM31; 64],
        pub(crate) low: [QM31; 16],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Selectors { }
    #[automatically_derived]
    impl ::core::clone::Clone for Selectors {
        #[inline]
        fn clone(&self) -> Selectors {
            let _: ::core::clone::AssertParamIsClone<[QM31; 64]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 16]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Selectors { }
    impl Selectors {
        fn expand<const N :
            usize>(point: &[QM31; 10], start: usize, count: usize)
            -> [QM31; N] {
            let mut weights = [QM31::ZERO; N];
            weights[0] = QM31::ONE;
            let mut len = 1usize;
            let mut coordinate = start;
            while coordinate < start + count {
                let prepared = PreparedQm31Multiplier::new(point[coordinate]);
                let mut index = len;
                while index > 0 {
                    index -= 1;
                    let parent = weights[index];
                    let right = prepared.mul(parent);
                    weights[2 * index] = parent.sub(right);
                    weights[2 * index + 1] = right;
                }
                len *= 2;
                coordinate += 1;
            }
            weights
        }
        pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
            Self {
                high: Self::expand(point, 0, 6),
                low: Self::expand(point, 6, 4),
            }
        }
        #[inline(never)]
        pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Self {
            Self::at_point(point)
        }
        #[inline(always)]
        pub(crate) fn row(&self, row: usize) -> QM31 {
            if false {
                if !(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1) {
                    ::core::panicking::panic("assertion failed: row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1")
                };
            };
            self.high[row >> 4].mul(self.low[row & 15])
        }
        fn active_literal(&self) -> QM31 {
            let mut sum = QM31::ZERO;
            let mut block = 0usize;
            while block < 64 {
                let mask = constants::ACTIVE_ROW_MASKS[block];
                if mask != 0 {
                    sum =
                        sum.add(self.high[block].mul(selector_mask_sum_16(&self.low,
                                    mask)));
                }
                block += 1;
            }
            sum
        }
        #[inline(always)]
        fn active(&self) -> QM31 { return self.active_literal(); }
    }
    fn pattern_values_literal(openings: &[QM31; POSEIDON2_WIDTH],
        lambda: QM31)
        -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
        let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
        let mut power = lambda;
        let mut limb = 0usize;
        while limb < POSEIDON2_WIDTH {
            powers[limb] = power;
            power = power.mul(lambda);
            limb += 1;
        }
        let mut result =
            [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
        let mut pattern_index = 0usize;
        while pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 {
            let pattern = constants::COPY_PATTERNS[pattern_index];
            let mut value = QM31::ZERO;
            limb = 0;
            while limb < POSEIDON2_WIDTH {
                if pattern.kinds[limb] == 1 {
                    let source =
                        openings[usize::from(pattern.columns[limb])].add(lift_m31(M31(pattern.offsets[limb])));
                    value = value.add(powers[limb].mul(source));
                }
                limb += 1;
            }
            result[pattern_index] = value;
            pattern_index += 1;
        }
        result
    }
    fn pattern_values(openings: &[QM31; POSEIDON2_WIDTH], lambda: QM31)
        -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
        return pattern_values_literal(openings, lambda);
    }
    struct CopyRowExtension {
        producer_values: [QM31; 2],
        producer_weights: [QM31; 2],
        consumer_values: [QM31; 2],
        consumer_weights: [QM31; 2],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CopyRowExtension { }
    #[automatically_derived]
    impl ::core::clone::Clone for CopyRowExtension {
        #[inline]
        fn clone(&self) -> CopyRowExtension {
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CopyRowExtension { }
    fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
        let denominators =
            [chi.sub(row.producer_values[0]), chi.sub(row.producer_values[1]),
                    chi.sub(row.consumer_values[0]),
                    chi.sub(row.consumer_values[1])];
        let producer_denominator = denominators[0].mul(denominators[1]);
        let consumer_denominator = denominators[2].mul(denominators[3]);
        let producer_numerator =
            row.producer_weights[0].mul(denominators[1]).add(row.producer_weights[1].mul(denominators[0]));
        let consumer_numerator =
            row.consumer_weights[0].mul(denominators[3]).add(row.consumer_weights[1].mul(denominators[2]));
        producer_denominator.mul(helper.mul(consumer_denominator).add(consumer_numerator)).sub(consumer_denominator.mul(producer_numerator))
    }
    #[inline(always)]
    fn link_weight(link: CompiledPoolV1PairForestLink, append_index: u64,
        variant: PoolV1PairForestCompiledVariantV1) -> M31 {
        match link.weight_kind {
            0 => M31::ONE,
            1 =>
                M31(u32::from(variant ==
                            PoolV1PairForestCompiledVariantV1::PrivateTransfer)),
            2 =>
                M31(u32::from(variant ==
                            PoolV1PairForestCompiledVariantV1::Withdrawal)),
            3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),
            4 => M31(((append_index >> link.weight_level) & 1) as u32),
            _ => {
                ::core::panicking::panic_fmt(format_args!("internal error: entered unreachable code: {0}",
                        format_args!("generated Pool V1 pair-forest Copy weight")));
            }
        }
    }
    fn accumulate_endpoint(values: &mut [QM31; 2], weights: &mut [QM31; 2],
        endpoint: CompiledPoolV1PairForestEndpoint, tag: u32, weight: M31,
        patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
        selectors: &Selectors) {
        let selector = selectors.row(usize::from(endpoint.row));
        let slot = usize::from(endpoint.slot);
        { weights[slot] = weights[slot].add(selector.mul_m31(weight)); }
        let compressed =
            lift_m31(M31(tag)).add(patterns[usize::from(endpoint.pattern)]);
        values[slot] = values[slot].add(selector.mul(compressed));
    }
    pub(crate) fn evaluate_with_selectors(openings: &[QM31; POSEIDON2_WIDTH],
        h1_z: QM31, selectors: &Selectors, lambda: QM31, chi: QM31,
        append_index: u64, variant: PoolV1PairForestCompiledVariantV1)
        -> PoolV1PairForestCompiledCopyTerminalV1 {
        let patterns = pattern_values(openings, lambda);
        let mut row =
            CopyRowExtension {
                producer_values: [QM31::ZERO; 2],
                producer_weights: [QM31::ZERO; 2],
                consumer_values: [QM31::ZERO; 2],
                consumer_weights: [QM31::ZERO; 2],
            };
        let mut link_index = 0usize;
        while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
            let link = constants::COPY_LINKS[link_index];
            let weight = link_weight(link, append_index, variant);
            {
                accumulate_endpoint(&mut row.producer_values,
                    &mut row.producer_weights, link.producer, link.tag, weight,
                    &patterns, selectors);
                accumulate_endpoint(&mut row.consumer_values,
                    &mut row.consumer_weights, link.consumer, link.tag, weight,
                    &patterns, selectors);
            }
            link_index += 1;
        }
        let active = selectors.active();
        PoolV1PairForestCompiledCopyTerminalV1 {
            residual: active.mul(copy_residual(row, h1_z, chi)),
            active,
        }
    }
    /// Evaluate the exact 136-link pair-forest Copy lane from the frozen sixteen
    /// merged-C1 openings and one H1 opening. This performs one fixed-size
    /// selector allocation and, under the selected tensor-basis evaluator, one
    /// fixed 103-QM31 scratch allocation. There is no registry- or input-dependent
    /// allocation.
    pub fn evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(openings:
            &[QM31; POSEIDON2_WIDTH], h1_z: QM31, point: &[QM31; 10],
        lambda: QM31, chi: QM31, append_index: u64,
        variant: PoolV1PairForestCompiledVariantV1)
        -> PoolV1PairForestCompiledCopyTerminalV1 {
        let selectors = Selectors::boxed_at_point(point);
        evaluate_with_selectors(openings, h1_z, &selectors, lambda, chi,
            append_index, variant)
    }
    pub fn pool_v1_pair_forest_copy_active_at_point_compiled_v1(point:
            &[QM31; 10]) -> QM31 {
        Selectors::at_point(point).active()
    }
    /// Source-extraction wrapper for a Boolean terminal row. `variant` is zero
    /// for private transfer and one for withdrawal.
    #[doc(hidden)]
    pub fn pool_v1_pair_forest_copy_lane_boolean_extraction_v1(variant: u8,
        selected_row: u16, openings: &[QM31; POSEIDON2_WIDTH], h1_z: QM31,
        lambda: QM31, chi: QM31, append_index: u64)
        -> Option<PoolV1PairForestCompiledCopyTerminalV1> {
        if usize::from(selected_row) >=
                POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1 {
            return None;
        }
        let variant =
            match variant {
                0 => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
                1 => PoolV1PairForestCompiledVariantV1::Withdrawal,
                _ => return None,
            };
        let mut high = [QM31::ZERO; 64];
        let mut low = [QM31::ZERO; 16];
        high[usize::from(selected_row >> 4)] = QM31::ONE;
        low[usize::from(selected_row & 15)] = QM31::ONE;
        let selectors = Selectors { high, low };
        Some(evaluate_with_selectors(openings, h1_z, &selectors, lambda, chi,
                append_index, variant))
    }
    #[inline(always)]
    fn pattern_window(openings: &[QM31; POSEIDON2_WIDTH],
        prepared: [PreparedQm31Multiplier; 8], start: usize) -> QM31 {
        let mut value = QM31::ZERO;
        let mut slot = 0usize;
        while slot < 8 {
            value = value.add(prepared[slot].mul(openings[start + slot]));
            slot += 1;
        }
        value
    }
}
pub mod host_terminal {
    //! Allocation-bounded selected terminal for the eight-lane Pool V1 pair
    //! forest. The relation keeps the frozen Tag-73 three-opening geometry and
    //! packs Poseidon, 94 semantic source lanes and the 136-link Copy argument
    //! into the same 29 theta lanes as the one-tree payment terminal.
    macro_rules! qm31_array {
        ($n:expr, $index:ident, $body:expr) =>
        {{
                let mut output = [QM31::ZERO; $n]; let mut $index = 0usize;
                while $index < $n { output[$index] = $body; $index += 1; }
                output
            }};
    }
    use crate::host_terminal_field::{qm31_pack_base4, PreparedQm31Multiplier};
    use aspis_core::{
        field::{CM31, M31, QM31},
        state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
    };
    use aspis_statement::{
        poseidon2::{
            Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK,
            POSEIDON2_WIDTH, RATE,
        },
        state_only_poseidon::{
            evaluate_state_only_poseidon_oracle_projected,
            StateOnlyPoseidonOpenings, StateOnlyPoseidonSelectors,
        },
    };
    use aspis_statement::pool_v1::{
        pair_tree_profile::{
            PoolV1PairLatePublicStatementV1, POOL_V1_PAIR_CAPACITY,
        },
        payment_relation::{
            PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
        },
    };
    use aspis_prover::host_arithmetic::state_only_selected_mask_value;
    use crate::host_copy_terminal::{
        evaluate_with_selectors, PoolV1PairForestCompiledVariantV1, Selectors,
    };
    const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);
    const DOMAIN_NULLIFIER: M31 = M31(0x4153_0002);
    const DOMAIN_NOTE: M31 = M31(0x4153_0003);
    pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1: usize = 1024;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1: usize = 16;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1: usize = 3;
    pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 +
                STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
    pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1 *
            POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1;
    pub const POOL_V1_PAIR_FOREST_SOURCE_SEMANTIC_LANES_V1: usize = 94;
    pub const POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1: usize = 24;
    pub const POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1: usize = 4;
    pub const POOL_V1_PAIR_FOREST_COPY_LANES_V1: usize = 1;
    pub const POOL_V1_PAIR_FOREST_THETA_LANES_V1: usize =
        POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1 +
                POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1 +
            POOL_V1_PAIR_FOREST_COPY_LANES_V1;
    pub const POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1: usize =
        POOL_V1_PAIR_FOREST_THETA_LANES_V1 - 1;
    pub const POOL_V1_PAIR_FOREST_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE_V1: usize
        =
        26;
    pub const POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1:
        usize =
        27;
    pub const POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1: usize = 27;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
        if false { 2 } else { 1 };
    pub const POOL_V1_PAIR_FOREST_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
        core::mem::size_of::<Selectors>();
    const SELECTED_H1_COLUMN: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 +
            STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
    const VALUE_AUXILIARY_BLOCK: usize = 63;
    const INPUT_OCCUPANCY_ROW: usize = 63 * 16 + 9;
    const OUTPUT_OCCUPANCY_ROW: usize = 63 * 16 + 10;
    const _: () =
        if !(DIGEST_ELEMS == 8) {
            ::core::panicking::panic("assertion failed: DIGEST_ELEMS == 8")
        };
    const _: () =
        if !(POSEIDON2_WIDTH == 16) {
            ::core::panicking::panic("assertion failed: POSEIDON2_WIDTH == 16")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28")
        };
    mod constants {
        pub const POOL_V1_PAIR_EMPTY_ROOTS_V1: [[u32; 8]; 21] =
            [[1438900896, 782233260, 1544844157, 891350894, 986827501,
                            300047813, 266092546, 1155026732],
                    [141619947, 1448060902, 524379093, 1944458907, 1832113773,
                            579270723, 752346270, 1038346536],
                    [1119858538, 128294437, 939091034, 659145897, 1933666768,
                            903679201, 1182639487, 1398246146],
                    [1057897051, 1132946363, 794377079, 1971564389, 1255722275,
                            926653737, 2031728153, 2024887573],
                    [1410054462, 673771449, 940847521, 274330358, 1719505495,
                            1690439941, 203201419, 1855504616],
                    [1442759752, 1540325866, 188964047, 101815282, 1883549730,
                            1774537487, 1306717763, 561084592],
                    [244193611, 984304317, 1467689208, 2063463197, 1766003332,
                            1300835127, 1578947755, 745931587],
                    [673192756, 38070812, 1453532835, 1340577407, 368420458,
                            1834405704, 270061815, 711700631],
                    [27092219, 1272373356, 998194489, 1458413288, 887470405,
                            1204987730, 864453460, 553704718],
                    [1972918328, 1234090299, 977162835, 1704494754, 1617603773,
                            1819200880, 906453206, 1653526885],
                    [418360492, 472096212, 871749117, 98906847, 2026788776,
                            1504737042, 407274798, 1800828893],
                    [986339640, 660349625, 1012157959, 454024326, 987656904,
                            622864739, 1150440730, 1280042062],
                    [2118470693, 1706590589, 2128512933, 167263577, 409542414,
                            1323179656, 1880070613, 2053396184],
                    [260546973, 1375125357, 1584234519, 1097072342, 1685367984,
                            1070989054, 2113798037, 958210542],
                    [1239966481, 992485427, 1397515674, 466658549, 2071909237,
                            712995354, 2047452742, 1680224983],
                    [1796237568, 1862343136, 1954463912, 1190686266, 364700025,
                            46960257, 671215600, 1214723477],
                    [1127845264, 662862400, 84021756, 995080286, 1419670571,
                            1966281459, 837284626, 2083375353],
                    [1321679286, 782621548, 1415820264, 74436574, 776350425,
                            323154748, 429051705, 1299980413],
                    [1519171444, 1235587172, 1671492368, 1449613582, 547369941,
                            1621086153, 266860322, 450526803],
                    [19381883, 1308966873, 251977766, 474343397, 2069732268,
                            1863820229, 152153379, 665567443],
                    [1201428963, 1296676114, 441891487, 1910121140, 602621674,
                            1294160489, 1878016864, 855887413]];
    }
    pub enum PoolV1PairForestSemanticTerminalErrorV1 {
        InvalidPublicAmount,
        InvalidAppendTransition,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestSemanticTerminalErrorV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestSemanticTerminalErrorV1 { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestSemanticTerminalErrorV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount
                        => "InvalidPublicAmount",
                    PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition
                        => "InvalidAppendTransition",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestSemanticTerminalErrorV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestSemanticTerminalErrorV1)
            -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    enum CompiledVariant { PrivateTransfer, Withdrawal, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CompiledVariant { }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledVariant {
        #[inline]
        fn clone(&self) -> CompiledVariant { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledVariant { }
    #[automatically_derived]
    impl ::core::fmt::Debug for CompiledVariant {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    CompiledVariant::PrivateTransfer => "PrivateTransfer",
                    CompiledVariant::Withdrawal => "Withdrawal",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for CompiledVariant { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for CompiledVariant {
        #[inline]
        fn eq(&self, other: &CompiledVariant) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for CompiledVariant {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    struct SemanticPublic {
        variant: CompiledVariant,
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        nullifier: Digest,
        asset_id: M31,
        recipient: Option<Digest>,
        change: Digest,
        withdrawal_amount: Option<u32>,
        transition: PoolV1PairLatePublicStatementV1,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for SemanticPublic { }
    #[automatically_derived]
    impl ::core::clone::Clone for SemanticPublic {
        #[inline]
        fn clone(&self) -> SemanticPublic {
            let _: ::core::clone::AssertParamIsClone<CompiledVariant>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            let _: ::core::clone::AssertParamIsClone<Digest>;
            let _: ::core::clone::AssertParamIsClone<M31>;
            let _: ::core::clone::AssertParamIsClone<Option<Digest>>;
            let _: ::core::clone::AssertParamIsClone<Option<u32>>;
            let _:
                    ::core::clone::AssertParamIsClone<PoolV1PairLatePublicStatementV1>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for SemanticPublic { }
    #[inline(always)]
    fn lift_m31(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    /// Count only the trailing one bits used by the twenty-level append tree.
    /// The bounded form is equivalent to capping u64::trailing_ones at twenty.
    fn bounded_append_carry(mut index: u64) -> usize {
        let mut carry = 0usize;
        while carry < 20 {
            if index & 1 == 0 { return carry; }
            index >>= 1u32;
            carry += 1;
        }
        carry
    }
    #[inline(always)]
    fn add_preweighted<const N :
        usize>(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        start: usize, values: &[QM31; N]) {
        let first = start / 4;
        let last = (start + N - 1) / 4;
        for group in first..=last {
            let lanes: [QM31; 4] =
                {
                    let mut output = [QM31::ZERO; 4];
                    let mut slot = 0usize;
                    while slot < 4 {
                        output[slot] =
                            {
                                let source = 4 * group + slot;
                                if source >= start && source < start + N {
                                    values[source - start]
                                } else { QM31::ZERO }
                            };
                        slot += 1;
                    }
                    output
                };
            packed[group] = packed[group].add(qm31_pack_base4(&lanes));
        }
    }
    #[inline(always)]
    fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>])
        -> QM31 {
        let mut sum = QM31::ZERO;
        for range in ranges {
            for block in range.clone() {
                sum = sum.add(selectors.high[block]);
            }
        }
        sum
    }
    #[inline(always)]
    fn reconstruct_10(view: &[QM31; 16]) -> QM31 {
        let mut acc = view[9];
        let mut index = 9usize;
        while index > 0 { index -= 1; acc = acc.add(acc).add(view[index]); }
        acc
    }
    #[inline(always)]
    fn empty_root(level: usize) -> Digest {
        let words = constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level];
        [M31(words[0]), M31(words[1]), M31(words[2]), M31(words[3]),
                M31(words[4]), M31(words[5]), M31(words[6]), M31(words[7])]
    }
    fn validate_transition(public: SemanticPublic)
        -> Result<(), PoolV1PairForestSemanticTerminalErrorV1> {
        let source = public.transition.live_snapshot;
        let after = public.transition.candidate_afterstate;
        if source.pool != public.pool ||
                            source.deployment_domain != public.deployment_domain ||
                        source.sequence != source.next_pair_index ||
                    source.next_pair_index >= POOL_V1_PAIR_CAPACITY ||
                source.next_pair_index.checked_add(1) !=
                    Some(after.next_pair_index) {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
        }
        let index = source.next_pair_index;
        let carry = bounded_append_carry(index);
        for level in 0..20 {
            if level == carry && carry < 20 { continue; }
            let expected =
                if level < carry || ((index >> level) & 1) == 0 {
                    empty_root(level)
                } else { source.frontier[level] };
            if after.next_frontier[level] != expected {
                return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
            }
        }
        Ok(())
    }
    fn poseidon_selectors(selectors: &Selectors)
        -> StateOnlyPoseidonSelectors {
        StateOnlyPoseidonSelectors {
            block: sum_high(selectors, &[0..57]),
            local: selectors.low,
        }
    }
    #[inline(never)]
    fn initial_variant_selectors(variant: CompiledVariant, high27: QM31,
        high28: QM31, high29: QM31) -> (QM31, QM31, QM31, QM31) {
        match variant {
            CompiledVariant::PrivateTransfer =>
                (high27, QM31::ZERO, high27.add(high28), high29),
            CompiledVariant::Withdrawal =>
                (QM31::ZERO, high27.add(high28).add(high29), QM31::ZERO,
                    QM31::ZERO),
        }
    }
    fn semantic_initial_and_absorption(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> ([QM31; 16], [QM31; 16]) {
        let nodes = sum_high(selectors, &[4..25, 33..57]);
        let first_common =
            selectors.high[0].add(selectors.high[1]).add(selectors.high[25]).add(selectors.high[30]);
        let (transfer_first, fixed, private_chunk_eight, private_chunk_two) =
            initial_variant_selectors(public.variant, selectors.high[27],
                selectors.high[28], selectors.high[29]);
        let full_initial_selector =
            selectors.low[0].mul(first_common.add(transfer_first).add(fixed));
        let rate_initial_selector = selectors.low[0].mul(nodes);
        let full = PreparedQm31Multiplier::new(full_initial_selector);
        let full_or_rate =
            PreparedQm31Multiplier::new(full_initial_selector.add(rate_initial_selector));
        let mut initial =
            {
                let mut output = [QM31::ZERO; 16];
                let mut lane = 0usize;
                while lane < 16 {
                    output[lane] =
                        {
                            if lane < RATE {
                                full_or_rate.mul(openings.z[lane])
                            } else { full.mul(openings.z[lane]) }
                        };
                    lane += 1;
                }
                output
            };
        let note_first =
            selectors.high[1].add(selectors.high[30]).add(transfer_first);
        let domain =
            selectors.high[0].mul_m31(DOMAIN_OWNER_KEY).add(note_first.mul_m31(DOMAIN_NOTE)).add(selectors.high[25].mul_m31(DOMAIN_NULLIFIER));
        let length =
            selectors.high[0].mul_m31(M31(8)).add(note_first.mul_m31(M31(18))).add(selectors.high[25].mul_m31(M31(16)));
        initial[RATE] = initial[RATE].sub(selectors.low[0].mul(domain));
        initial[RATE + 1] =
            initial[RATE + 1].sub(selectors.low[0].mul(length));
        let mut chunk_eight =
            selectors.high[0].add(selectors.high[1]).add(selectors.high[2]).add(selectors.high[25]).add(selectors.high[26]).add(selectors.high[30]).add(selectors.high[31]);
        let mut chunk_two = selectors.high[3].add(selectors.high[32]);
        chunk_eight = chunk_eight.add(private_chunk_eight);
        chunk_two = chunk_two.add(private_chunk_two);
        let absorption =
            absorption_lanes_literal(selectors.low[12], fixed, chunk_two,
                chunk_eight, nodes, &openings.z);
        (initial, absorption)
    }
    fn absorption_lanes_literal(low: QM31, fixed: QM31, chunk_two: QM31,
        chunk_eight: QM31, nodes: QM31, openings: &[QM31; 16]) -> [QM31; 16] {
        {
            let mut output = [QM31::ZERO; 16];
            let mut lane = 0usize;
            while lane < 16 {
                output[lane] =
                    {
                        let blocks =
                            if lane < 2 {
                                fixed
                            } else if lane < RATE {
                                fixed.add(chunk_two)
                            } else { fixed.add(chunk_two).add(chunk_eight).add(nodes) };
                        low.mul(blocks).mul(openings[lane])
                    };
                lane += 1;
            }
            output
        }
    }
    #[inline(always)]
    fn add_digest_binding(output: &mut [QM31; DIGEST_ELEMS], selector: QM31,
        opened: &[QM31; POSEIDON2_WIDTH], start: usize, expected: &Digest,
        right_tweak: bool) {
        for lane in 0..DIGEST_ELEMS {
            let mut target = expected[lane];
            if right_tweak && lane + 1 == DIGEST_ELEMS {
                target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
            }
            output[lane] =
                output[lane].add(selector.mul(opened[start +
                                    lane].sub(lift_m31(target))));
        }
    }
    #[inline(never)]
    fn add_schedule_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        public: SemanticPublic, openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors) {
        let (initial, absorption) =
            semantic_initial_and_absorption(public, openings, selectors);
        add_preweighted(packed, 0, &initial);
        add_preweighted(packed, 16, &absorption);
    }
    #[inline(never)]
    fn add_path_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors) {
        let path_selector =
            sum_high(selectors,
                    &[57..63]).mul(selectors.low[1].add(selectors.low[5]).add(selectors.low[9]).add(selectors.low[13]));
        let path = path_lanes_literal(path_selector, openings);
        add_preweighted(packed, 32, &path);
    }
    fn path_lanes_literal(path_selector: QM31,
        openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
        let bit = openings.z[0];
        let mut path = [QM31::ZERO; 17];
        path[0] = path_selector.mul(bit.mul(bit.sub(QM31::ONE)));
        for lane in 0..DIGEST_ELEMS {
            let current = openings.z[1 + lane];
            path[1 + lane] =
                path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[lane].sub(current));
            path[1 + DIGEST_ELEMS + lane] =
                path_selector.mul(bit).mul(openings.succ_z[RATE +
                                lane].sub(current));
        }
        path
    }
    #[inline(never)]
    fn add_value_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors) {
        let value_selectors =
            [selectors.row(16 * VALUE_AUXILIARY_BLOCK),
                    selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2),
                    selectors.row(16 * VALUE_AUXILIARY_BLOCK + 4)];
        let range_selector =
            QM31::ZERO.add(value_selectors[0]).add(value_selectors[1]).add(value_selectors[2]);
        let mut range = [QM31::ZERO; 33];
        let mut index = 0usize;
        while index < 10 {
            range[index] = openings.z[index].square().sub(openings.z[index]);
            index += 1;
        }
        index = 0;
        while index < 10 {
            range[10 + index] =
                openings.succ_z[index].square().sub(openings.succ_z[index]);
            index += 1;
        }
        index = 0;
        while index < 10 {
            range[20 + index] =
                openings.xor12_z[index].square().sub(openings.xor12_z[index]);
            index += 1;
        }
        let reconstructed =
            reconstruct_10(&openings.z).add(reconstruct_10(&openings.succ_z).mul_m31(M31(1
                                <<
                                10))).add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 <<
                            20)));
        range[30] = openings.z[10].sub(reconstructed);
        range[31] = openings.succ_z[10];
        range[32] = openings.xor12_z[10];
        {
            for residual in &mut range {
                *residual = range_selector.mul(*residual);
            }
            add_preweighted(packed, 49, &range);
        }
        let conservation_selector =
            selectors.row(16 * VALUE_AUXILIARY_BLOCK + 6);
        let conservation =
            [conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
                    conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1]))];
        add_preweighted(packed, 82, &conservation);
    }
    #[inline(never)]
    fn variant_expected_output(variant: CompiledVariant) -> M31 {
        match variant {
            CompiledVariant::PrivateTransfer => M31(1),
            CompiledVariant::Withdrawal => M31(0),
        }
    }
    #[inline(never)]
    fn add_occupancy_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        public: SemanticPublic, openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors) {
        let input_occupancy = selectors.row(INPUT_OCCUPANCY_ROW);
        let output_occupancy = selectors.row(OUTPUT_OCCUPANCY_ROW);
        let expected_output = variant_expected_output(public.variant);
        let occupancy =
            occupancy_lanes_literal(input_occupancy, output_occupancy,
                expected_output, &openings.z);
        add_preweighted(packed, 0, &occupancy);
    }
    fn occupancy_lanes_literal(input_occupancy: QM31, output_occupancy: QM31,
        expected_output: M31, opened: &[QM31; 16]) -> [QM31; 12] {
        let occupied = opened[0];
        let inverse = opened[1];
        let one_minus = QM31::ONE.sub(occupied);
        let mut occupancy = [QM31::ZERO; 12];
        let both = input_occupancy.add(output_occupancy);
        occupancy[0] = both.mul(occupied.mul(occupied.sub(QM31::ONE)));
        occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
        occupancy[2] = both.mul(one_minus.mul(inverse));
        for lane in 0..DIGEST_ELEMS {
            occupancy[3 + lane] = both.mul(one_minus.mul(opened[2 + lane]));
        }
        occupancy[11] =
            input_occupancy.mul(opened[10].mul(one_minus)).add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
        occupancy
    }
    #[inline(never)]
    fn public_digest_lanes(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> [QM31; DIGEST_ELEMS] {
        let mut digests = [QM31::ZERO; DIGEST_ELEMS];
        add_digest_binding(&mut digests, selectors.row(56 * 16 + 11),
            &openings.z, 0, &public.anchor, false);
        add_digest_binding(&mut digests, selectors.row(26 * 16 + 11),
            &openings.z, 0, &public.nullifier, false);
        if let Some(recipient) = public.recipient {
            add_digest_binding(&mut digests, selectors.row(29 * 16 + 11),
                &openings.z, 0, &recipient, false);
        }
        add_digest_binding(&mut digests, selectors.row(32 * 16 + 11),
            &openings.z, 0, &public.change, false);
        let source = public.transition.live_snapshot;
        let after = public.transition.candidate_afterstate;
        for level in 0..20 {
            let block = 34 + level;
            if ((source.next_pair_index >> level) & 1) == 0 {
                add_digest_binding(&mut digests, selectors.row(block * 16),
                    &openings.z, RATE, &empty_root(level), true);
            } else {
                add_digest_binding(&mut digests,
                    selectors.row(block * 16 + 12), &openings.z, 0,
                    &source.frontier[level], false);
            }
        }
        add_digest_binding(&mut digests, selectors.row(53 * 16 + 11),
            &openings.z, 0, &after.next_root, false);
        let carry = bounded_append_carry(source.next_pair_index);
        if carry < 20 {
            add_digest_binding(&mut digests,
                selectors.row((33 + carry) * 16 + 11), &openings.z, 0,
                &after.next_frontier[carry], false);
        }
        digests
    }
    #[inline(never)]
    fn scalar_lanes(variant: CompiledVariant, withdrawal_amount_present: bool,
        input_asset: QM31, mut output_scalar: QM31,
        private_transfer_term: QM31, withdrawal_term: QM31) -> [QM31; 2] {
        match variant {
            CompiledVariant::PrivateTransfer => {
                output_scalar = output_scalar.add(private_transfer_term);
            }
            CompiledVariant::Withdrawal => {
                if withdrawal_amount_present {
                    output_scalar = output_scalar.add(withdrawal_term);
                }
            }
        }
        [input_asset, output_scalar]
    }
    fn semantic_packed(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1] {
        let mut packed =
            [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
        add_schedule_lanes(&mut packed, public, openings, selectors);
        add_path_lanes(&mut packed, openings, selectors);
        add_value_lanes(&mut packed, openings, selectors);
        add_occupancy_lanes(&mut packed, public, openings, selectors);
        add_preweighted(&mut packed, 84,
            &public_digest_lanes(public, openings, selectors));
        let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
        let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
        let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
        let private_transfer_term =
            selectors.row(28 * 16 + 12).mul(asset_difference);
        let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
        let withdrawal_term =
            selectors.row(16 * VALUE_AUXILIARY_BLOCK +
                        2).mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
        let scalars =
            scalar_lanes(public.variant, public.withdrawal_amount.is_some(),
                input_asset, output_scalar, private_transfer_term,
                withdrawal_term);
        add_preweighted(&mut packed, 92, &scalars);
        packed
    }
    fn selected_claim(claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: usize, column: usize) -> QM31 {
        claims[point * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 +
                column]
    }
    #[inline(never)]
    fn copy_variant(variant: CompiledVariant)
        -> PoolV1PairForestCompiledVariantV1 {
        match variant {
            CompiledVariant::PrivateTransfer =>
                PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            CompiledVariant::Withdrawal =>
                PoolV1PairForestCompiledVariantV1::Withdrawal,
        }
    }
    fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
        let mut product = equality_factor(left[0], right[0]);
        let mut index = 1usize;
        while index < left.len() {
            product = product.mul(equality_factor(left[index], right[index]));
            index += 1;
        }
        product
    }
    #[allow(clippy::type_complexity)]
    fn composition_parts(public: SemanticPublic,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        ->
            Result<(QM31, [QM31; 16],
            [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], QM31, QM31, QM31),
            PoolV1PairForestSemanticTerminalErrorV1> {
        let invalid_amount =
            match public.withdrawal_amount {
                None => false,
                Some(amount) => amount == 0 || amount >= (1 << 30u32),
            };
        if invalid_amount {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
        }
        validate_transition(public)?;
        let openings =
            StateOnlyPoseidonOpenings {
                z: {
                    let mut output = [QM31::ZERO; 16];
                    let mut column = 0usize;
                    while column < 16 {
                        output[column] = selected_claim(claims, 0, column);
                        column += 1;
                    }
                    output
                },
                succ_z: {
                    let mut output = [QM31::ZERO; 16];
                    let mut column = 0usize;
                    while column < 16 {
                        output[column] = selected_claim(claims, 1, column);
                        column += 1;
                    }
                    output
                },
                xor12_z: {
                    let mut output = [QM31::ZERO; 16];
                    let mut column = 0usize;
                    while column < 16 {
                        output[column] = selected_claim(claims, 2, column);
                        column += 1;
                    }
                    output
                },
            };
        let mask_only =
            {
                let mut output =
                    [QM31::ZERO; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS];
                let mut column = 0usize;
                while column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
                    output[column] =
                        {
                            selected_claim(claims, 0,
                                POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column)
                        };
                    column += 1;
                }
                output
            };
        let selectors = Selectors::boxed_at_point(point);
        let poseidon =
            evaluate_state_only_poseidon_oracle_projected(&openings,
                &poseidon_selectors(&selectors));
        let semantic = semantic_packed(public, &openings, &selectors);
        let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
        let copy =
            evaluate_with_selectors(&openings.z, h1_z, &selectors, lambda,
                chi, public.transition.live_snapshot.next_pair_index,
                copy_variant(public.variant));
        let prepared_theta = PreparedQm31Multiplier::new(theta);
        let mut composition = copy.residual;
        let mut index = semantic.len();
        while index > 0 {
            index -= 1;
            composition =
                prepared_theta.mul(composition).add(semantic[index]);
        }
        index = poseidon.len();
        while index > 0 {
            index -= 1;
            composition =
                prepared_theta.mul(composition).add(poseidon[index]);
        }
        Ok((composition, openings.z, mask_only,
                selected_claim(claims, 0, SELECTED_G_COLUMN), h1_z,
                copy.active))
    }
    fn terminal_parts(public: SemanticPublic,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        ->
            Result<(QM31, [QM31; 16],
            [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], QM31),
            PoolV1PairForestSemanticTerminalErrorV1> {
        let (composition, c1, mask_only, g, h1_z, copy_active) =
            composition_parts(public, claims, point, lambda, chi, theta)?;
        let original =
            equality_value(zerocheck_point,
                            point).mul(composition).add(mu.mul(h1_z)).add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
        Ok((original, c1, mask_only, g))
    }
    fn private_public<'a>(public: &PoolV1PrivateTransferPublicV1,
        transition: &'a PoolV1PairLatePublicStatementV1) -> SemanticPublic {
        SemanticPublic {
            variant: CompiledVariant::PrivateTransfer,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: Some(public.recipient_commitment),
            change: public.change_commitment,
            withdrawal_amount: None,
            transition: *transition,
        }
    }
    fn withdrawal_public<'a>(public: &PoolV1WithdrawalPublicV1,
        transition: &'a PoolV1PairLatePublicStatementV1) -> SemanticPublic {
        SemanticPublic {
            variant: CompiledVariant::Withdrawal,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: None,
            change: public.change_commitment,
            withdrawal_amount: Some(public.amount),
            transition: *transition,
        }
    }
    macro_rules! define_variant_terminal {
        ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty,
        $convert:ident) =>
        {
            #[allow(clippy::too_many_arguments)] pub fn
            $composition(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,) ->
            Result<QM31, PoolV1PairForestSemanticTerminalErrorV1>
            {
                Ok(composition_parts($convert(public, transition), claims,
                point, lambda, chi, theta,)? .0)
            } #[allow(clippy::too_many_arguments)] pub fn
            $unmasked(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
            zerocheck_point: &[QM31; 10], mu: QM31,) -> Result<QM31,
            PoolV1PairForestSemanticTerminalErrorV1>
            {
                Ok(terminal_parts($convert(public, transition), claims, point,
                lambda, chi, theta, zerocheck_point, mu,)? .0)
            } #[allow(clippy::too_many_arguments)] #[inline(never)] pub fn
            $masked(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
            zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31,) ->
            Result<QM31, PoolV1PairForestSemanticTerminalErrorV1>
            {
                let (original, c1, mask_only, g) =
                terminal_parts($convert(public, transition), claims, point,
                lambda, chi, theta, zerocheck_point, mu,)?;
                Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                point).add(eta.mul(original)))
            }
        };
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(composition_parts(private_public(public, transition), claims,
                        point, lambda, chi, theta)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(terminal_parts(private_public(public, transition), claims, point,
                        lambda, chi, theta, zerocheck_point, mu)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    #[inline(never)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        let (original, c1, mask_only, g) =
            terminal_parts(private_public(public, transition), claims, point,
                    lambda, chi, theta, zerocheck_point, mu)?;
        Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                    point).add(eta.mul(original)))
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(composition_parts(withdrawal_public(public, transition), claims,
                        point, lambda, chi, theta)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(terminal_parts(withdrawal_public(public, transition), claims,
                        point, lambda, chi, theta, zerocheck_point, mu)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    #[inline(never)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        let (original, c1, mask_only, g) =
            terminal_parts(withdrawal_public(public, transition), claims,
                    point, lambda, chi, theta, zerocheck_point, mu)?;
        Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                    point).add(eta.mul(original)))
    }
    /// R0's width-29 view of this exact pair-forest terminal. No generic Spend
    /// terminal, legacy transcript or legacy claim stride is selected here.
    pub mod r0 {
        use super::*;
        use alloc::vec::Vec;
        use aspis_core::field::WideExact;
        use aspis_core::state_only_prefix::r0::{
            Challenges, Error, PointClaims,
        };
        pub enum Public<'a> {
            Transfer(&'a PoolV1PrivateTransferPublicV1,
                &'a PoolV1PairLatePublicStatementV1),
            Withdrawal(&'a PoolV1WithdrawalPublicV1,
                &'a PoolV1PairLatePublicStatementV1),
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl<'a> ::core::clone::TrivialClone for Public<'a> { }
        #[automatically_derived]
        impl<'a> ::core::clone::Clone for Public<'a> {
            #[inline]
            fn clone(&self) -> Public<'a> {
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PrivateTransferPublicV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PairLatePublicStatementV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1WithdrawalPublicV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PairLatePublicStatementV1>;
                *self
            }
        }
        #[automatically_derived]
        impl<'a> ::core::marker::Copy for Public<'a> { }
        impl<'a> Public<'a> {
            fn semantic(self) -> SemanticPublic {
                match self {
                    Self::Transfer(public, transition) =>
                        private_public(public, transition),
                    Self::Withdrawal(public, transition) =>
                        withdrawal_public(public, transition),
                }
            }
            pub fn transition(self) -> &'a PoolV1PairLatePublicStatementV1 {
                match self {
                    Self::Transfer(_, t) | Self::Withdrawal(_, t) => t,
                }
            }
            /// SPEC §9 declaration order. Pool/domain/sequence and source current
            /// root are not fields of R0P.Public and are not silently hashed here.
            /// Existing reject-only public guards remain in the terminal.
            pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
                fn fields(out: &mut Vec<u8>, values: &[M31])
                    -> Result<(), Error> {
                    for value in values {
                        if value.0 >= aspis_core::field::P {
                            return Err(Error::Public);
                        }
                        out.extend_from_slice(&value.0.to_le_bytes());
                    }
                    Ok(())
                }
                fn frontier(out: &mut Vec<u8>, values: &[Digest; 20])
                    -> Result<(), Error> {
                    fields(out, &values[0])?;
                    fields(out, &values[1])?;
                    fields(out, &values[2])?;
                    fields(out, &values[3])?;
                    fields(out, &values[4])?;
                    fields(out, &values[5])?;
                    fields(out, &values[6])?;
                    fields(out, &values[7])?;
                    fields(out, &values[8])?;
                    fields(out, &values[9])?;
                    fields(out, &values[10])?;
                    fields(out, &values[11])?;
                    fields(out, &values[12])?;
                    fields(out, &values[13])?;
                    fields(out, &values[14])?;
                    fields(out, &values[15])?;
                    fields(out, &values[16])?;
                    fields(out, &values[17])?;
                    fields(out, &values[18])?;
                    fields(out, &values[19])?;
                    Ok(())
                }
                let p = self.semantic();
                let mut out = Vec::new();
                out.push(match p.variant {
                        CompiledVariant::PrivateTransfer => 0,
                        CompiledVariant::Withdrawal => 1,
                    });
                fields(&mut out, &p.anchor)?;
                fields(&mut out, &p.nullifier)?;
                fields(&mut out, &[p.asset_id])?;
                out.push(u8::from(p.recipient.is_some()));
                if let Some(value) = p.recipient {
                    fields(&mut out, &value)?;
                }
                fields(&mut out, &p.change)?;
                out.push(u8::from(p.withdrawal_amount.is_some()));
                if let Some(value) = p.withdrawal_amount {
                    fields(&mut out, &[M31(value)])?;
                }
                let source = p.transition.live_snapshot;
                let after = p.transition.candidate_afterstate;
                out.extend_from_slice(&source.next_pair_index.to_le_bytes());
                frontier(&mut out, &source.frontier)?;
                fields(&mut out, &after.next_root)?;
                frontier(&mut out, &after.next_frontier)?;
                Ok(out)
            }
            /// Fast K path. D is deliberately absent from the terminal formula,
            /// but its three claims remain in the width-29 opening statement.
            pub fn terminal_qm31(self, claims: &[[QM31; 29]; 3],
                alpha: &[QM31; 10], c: &Challenges) -> Result<QM31, Error> {
                let mut selected = [QM31::ZERO; 84];
                let mut i = 0usize;
                while i < 84 { selected[i] = claims[i / 28][i % 28]; i += 1; }
                match terminal_parts(self.semantic(), &selected, alpha,
                        c.lambda, c.chi, c.theta, &c.zc, c.mu) {
                    Ok(parts) => Ok(parts.0),
                    Err(_) => Err(Error::Public),
                }
            }
            /// Extend the existing polynomial evaluator to E without narrowing
            /// adversarial E claims. At fixed K coordinates, substituting
            /// c0+t*c1 for every claim gives degree <=25: the Poseidon evaluator
            /// has two consecutive fifth powers (5*5); Copy has four affine
            /// denominators times H1 (degree 5); the other families have degree
            /// <=3. Selectors, theta, mu and equality weights are constants here.
            /// Hence 26 K evaluations determine its value at t=v exactly.
            /// This is polynomial base extension, not a probabilistic identity
            /// test. The honest K path requires only one terminal evaluation.
            pub fn terminal(self, claims: &PointClaims, alpha: &[QM31; 10],
                c: &Challenges) -> Result<WideExact, Error> {
                if claims.iter().flatten().all(|x| x.c1() == QM31::ZERO) {
                    let values = terminal_values(claims, None);
                    return self.terminal_qm31(&values, alpha,
                                c).map(WideExact::from_qm31);
                }
                let mut total = WideExact::ZERO;
                for i in 0..26u32 {
                    let values = terminal_values(claims, Some(M31(i)));
                    let value = self.terminal_qm31(&values, alpha, c)?;
                    let mut numerator = WideExact::ONE;
                    let mut denominator = M31::ONE;
                    for j in 0..26u32 {
                        if i == j { continue; }
                        numerator =
                            numerator.mul(WideExact::V.sub(WideExact::from_qm31(lift_m31(M31(j)))));
                        denominator = denominator.mul(M31(i).sub(M31(j)));
                    }
                    total =
                        total.add(numerator.mul_qm31(value.mul_m31(denominator.inv())));
                }
                Ok(total)
            }
        }
        #[inline(never)]
        fn terminal_values(claims: &PointClaims, t: Option<M31>)
            -> [[QM31; 29]; 3] {
            let mut values = [[QM31::ZERO; 29]; 3];
            for p in 0..3 {
                for l in 0..29 {
                    let x = claims[p][l];
                    values[p][l] =
                        match t {
                            None => x.c0(),
                            Some(t) => x.c0().add(x.c1().mul_m31(t)),
                        };
                }
            }
            values
        }
    }
    #[inline(always)]
    fn equality_factor(a: QM31, b: QM31) -> QM31 {
        let ab = a.mul(b);
        QM31::ONE.sub(a).sub(b).add(ab).add(ab)
    }
}
pub mod reference_terminal {
    //! Allocation-bounded selected terminal for the eight-lane Pool V1 pair
    //! forest. The relation keeps the frozen Tag-73 three-opening geometry and
    //! packs Poseidon, 94 semantic source lanes and the 136-link Copy argument
    //! into the same 29 theta lanes as the one-tree payment terminal.
    macro_rules! qm31_array {
        (4, $index:ident, $body:expr) =>
        {{
                let mut output=[QM31::ZERO;4];
                { let $index=0usize; output[0]=$body; }
                { let $index=1usize; output[1]=$body; }
                { let $index=2usize; output[2]=$body; }
                { let $index=3usize; output[3]=$body; } output
            }}; (16, $index:ident, $body:expr) =>
        {{
                let mut output=[QM31::ZERO;16];
                { let $index=0usize; output[0]=$body; }
                { let $index=1usize; output[1]=$body; }
                { let $index=2usize; output[2]=$body; }
                { let $index=3usize; output[3]=$body; }
                { let $index=4usize; output[4]=$body; }
                { let $index=5usize; output[5]=$body; }
                { let $index=6usize; output[6]=$body; }
                { let $index=7usize; output[7]=$body; }
                { let $index=8usize; output[8]=$body; }
                { let $index=9usize; output[9]=$body; }
                { let $index=10usize; output[10]=$body; }
                { let $index=11usize; output[11]=$body; }
                { let $index=12usize; output[12]=$body; }
                { let $index=13usize; output[13]=$body; }
                { let $index=14usize; output[14]=$body; }
                { let $index=15usize; output[15]=$body; } output
            }}; ($n:expr, $index:ident, $body:expr) =>
        {{
                let mut output = [QM31::ZERO; $n]; let mut $index = 0usize;
                while $index < $n { output[$index] = $body; $index += 1; }
                output
            }};
    }
    use crate::host_terminal_field::{qm31_pack_base4, PreparedQm31Multiplier};
    use aspis_core::{
        field::{CM31, M31, QM31},
        state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
    };
    use aspis_statement::{
        poseidon2::{
            Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK,
            POSEIDON2_WIDTH, RATE,
        },
        state_only_poseidon::{
            StateOnlyPoseidonOpenings, StateOnlyPoseidonSelectors,
        },
    };
    use aspis_statement::pool_v1::{
        pair_tree_profile::{
            PoolV1PairLatePublicStatementV1, POOL_V1_PAIR_CAPACITY,
        },
        payment_relation::{
            PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
        },
    };
    use aspis_prover::host_arithmetic::state_only_selected_mask_value;
    use crate::reference_copy_terminal::{
        evaluate_with_selectors, PoolV1PairForestCompiledVariantV1, Selectors,
    };
    const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);
    const DOMAIN_NULLIFIER: M31 = M31(0x4153_0002);
    const DOMAIN_NOTE: M31 = M31(0x4153_0003);
    pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1: usize = 1024;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1: usize = 16;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1: usize = 3;
    pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 +
                STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
    pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1 *
            POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1;
    pub const POOL_V1_PAIR_FOREST_SOURCE_SEMANTIC_LANES_V1: usize = 94;
    pub const POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1: usize = 24;
    pub const POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1: usize = 4;
    pub const POOL_V1_PAIR_FOREST_COPY_LANES_V1: usize = 1;
    pub const POOL_V1_PAIR_FOREST_THETA_LANES_V1: usize =
        POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1 +
                POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1 +
            POOL_V1_PAIR_FOREST_COPY_LANES_V1;
    pub const POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1: usize =
        POOL_V1_PAIR_FOREST_THETA_LANES_V1 - 1;
    pub const POOL_V1_PAIR_FOREST_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE_V1: usize
        =
        26;
    pub const POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1:
        usize =
        27;
    pub const POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1: usize = 27;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
        if false { 2 } else { 1 };
    pub const POOL_V1_PAIR_FOREST_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
        core::mem::size_of::<Selectors>();
    const SELECTED_H1_COLUMN: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 +
            STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
    const VALUE_AUXILIARY_BLOCK: usize = 63;
    const INPUT_OCCUPANCY_ROW: usize = 63 * 16 + 9;
    const OUTPUT_OCCUPANCY_ROW: usize = 63 * 16 + 10;
    const _: () =
        if !(DIGEST_ELEMS == 8) {
            ::core::panicking::panic("assertion failed: DIGEST_ELEMS == 8")
        };
    const _: () =
        if !(POSEIDON2_WIDTH == 16) {
            ::core::panicking::panic("assertion failed: POSEIDON2_WIDTH == 16")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28")
        };
    mod constants {
        pub const POOL_V1_PAIR_EMPTY_ROOTS_V1: [[u32; 8]; 21] =
            [[1438900896, 782233260, 1544844157, 891350894, 986827501,
                            300047813, 266092546, 1155026732],
                    [141619947, 1448060902, 524379093, 1944458907, 1832113773,
                            579270723, 752346270, 1038346536],
                    [1119858538, 128294437, 939091034, 659145897, 1933666768,
                            903679201, 1182639487, 1398246146],
                    [1057897051, 1132946363, 794377079, 1971564389, 1255722275,
                            926653737, 2031728153, 2024887573],
                    [1410054462, 673771449, 940847521, 274330358, 1719505495,
                            1690439941, 203201419, 1855504616],
                    [1442759752, 1540325866, 188964047, 101815282, 1883549730,
                            1774537487, 1306717763, 561084592],
                    [244193611, 984304317, 1467689208, 2063463197, 1766003332,
                            1300835127, 1578947755, 745931587],
                    [673192756, 38070812, 1453532835, 1340577407, 368420458,
                            1834405704, 270061815, 711700631],
                    [27092219, 1272373356, 998194489, 1458413288, 887470405,
                            1204987730, 864453460, 553704718],
                    [1972918328, 1234090299, 977162835, 1704494754, 1617603773,
                            1819200880, 906453206, 1653526885],
                    [418360492, 472096212, 871749117, 98906847, 2026788776,
                            1504737042, 407274798, 1800828893],
                    [986339640, 660349625, 1012157959, 454024326, 987656904,
                            622864739, 1150440730, 1280042062],
                    [2118470693, 1706590589, 2128512933, 167263577, 409542414,
                            1323179656, 1880070613, 2053396184],
                    [260546973, 1375125357, 1584234519, 1097072342, 1685367984,
                            1070989054, 2113798037, 958210542],
                    [1239966481, 992485427, 1397515674, 466658549, 2071909237,
                            712995354, 2047452742, 1680224983],
                    [1796237568, 1862343136, 1954463912, 1190686266, 364700025,
                            46960257, 671215600, 1214723477],
                    [1127845264, 662862400, 84021756, 995080286, 1419670571,
                            1966281459, 837284626, 2083375353],
                    [1321679286, 782621548, 1415820264, 74436574, 776350425,
                            323154748, 429051705, 1299980413],
                    [1519171444, 1235587172, 1671492368, 1449613582, 547369941,
                            1621086153, 266860322, 450526803],
                    [19381883, 1308966873, 251977766, 474343397, 2069732268,
                            1863820229, 152153379, 665567443],
                    [1201428963, 1296676114, 441891487, 1910121140, 602621674,
                            1294160489, 1878016864, 855887413]];
    }
    pub enum PoolV1PairForestSemanticTerminalErrorV1 {
        InvalidPublicAmount,
        InvalidAppendTransition,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestSemanticTerminalErrorV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestSemanticTerminalErrorV1 { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestSemanticTerminalErrorV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount
                        => "InvalidPublicAmount",
                    PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition
                        => "InvalidAppendTransition",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestSemanticTerminalErrorV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestSemanticTerminalErrorV1)
            -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    enum CompiledVariant { PrivateTransfer, Withdrawal, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CompiledVariant { }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledVariant {
        #[inline]
        fn clone(&self) -> CompiledVariant { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledVariant { }
    #[automatically_derived]
    impl ::core::fmt::Debug for CompiledVariant {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    CompiledVariant::PrivateTransfer => "PrivateTransfer",
                    CompiledVariant::Withdrawal => "Withdrawal",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for CompiledVariant { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for CompiledVariant {
        #[inline]
        fn eq(&self, other: &CompiledVariant) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for CompiledVariant {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub struct SemanticPublic {
        variant: CompiledVariant,
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        nullifier: Digest,
        asset_id: M31,
        recipient: Option<Digest>,
        change: Digest,
        withdrawal_amount: Option<u32>,
        transition: PoolV1PairLatePublicStatementV1,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for SemanticPublic { }
    #[automatically_derived]
    impl ::core::clone::Clone for SemanticPublic {
        #[inline]
        fn clone(&self) -> SemanticPublic {
            let _: ::core::clone::AssertParamIsClone<CompiledVariant>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            let _: ::core::clone::AssertParamIsClone<Digest>;
            let _: ::core::clone::AssertParamIsClone<M31>;
            let _: ::core::clone::AssertParamIsClone<Option<Digest>>;
            let _: ::core::clone::AssertParamIsClone<Option<u32>>;
            let _:
                    ::core::clone::AssertParamIsClone<PoolV1PairLatePublicStatementV1>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for SemanticPublic { }
    #[inline(always)]
    fn lift_m31(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    /// Count only the trailing one bits used by the twenty-level append tree.
    /// The bounded form is equivalent to capping u64::trailing_ones at twenty.
    fn bounded_append_carry(mut index: u64) -> usize {
        let mut carry = 0usize;
        while carry < 20 {
            if index & 1 == 0 { return carry; }
            index >>= 1u32;
            carry += 1;
        }
        carry
    }
    #[inline(always)]
    fn add_preweighted<const N :
        usize>(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        start: usize, values: &[QM31; N]) {
        let first = start / 4;
        let last = (start + N - 1) / 4;
        let mut group_index = first;
        while group_index <= last {
            let group = group_index;
            group_index += 1;
            let lanes: [QM31; 4] =
                {
                    let mut output = [QM31::ZERO; 4];
                    {
                        let slot = 0usize;
                        output[0] =
                            {
                                let source = 4 * group + slot;
                                if source >= start && source < start + N {
                                    values[source - start]
                                } else { QM31::ZERO }
                            };
                    }
                    {
                        let slot = 1usize;
                        output[1] =
                            {
                                let source = 4 * group + slot;
                                if source >= start && source < start + N {
                                    values[source - start]
                                } else { QM31::ZERO }
                            };
                    }
                    {
                        let slot = 2usize;
                        output[2] =
                            {
                                let source = 4 * group + slot;
                                if source >= start && source < start + N {
                                    values[source - start]
                                } else { QM31::ZERO }
                            };
                    }
                    {
                        let slot = 3usize;
                        output[3] =
                            {
                                let source = 4 * group + slot;
                                if source >= start && source < start + N {
                                    values[source - start]
                                } else { QM31::ZERO }
                            };
                    }
                    output
                };
            packed[group] = packed[group].add(qm31_pack_base4(&lanes));
        }
    }
    #[inline(always)]
    fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>])
        -> QM31 {
        let mut sum = QM31::ZERO;
        let mut range_index = 0usize;
        while range_index < ranges.len() {
            let mut block = ranges[range_index].start;
            while block < ranges[range_index].end {
                sum = sum.add(selectors.high[block]);
                block += 1;
            }
            range_index += 1;
        }
        sum
    }
    #[inline(always)]
    fn reconstruct_10(view: &[QM31; 16]) -> QM31 {
        let mut acc = view[9];
        let mut index = 9usize;
        acc = acc.add(acc).add(view[8usize]);
        acc = acc.add(acc).add(view[7usize]);
        acc = acc.add(acc).add(view[6usize]);
        acc = acc.add(acc).add(view[5usize]);
        acc = acc.add(acc).add(view[4usize]);
        acc = acc.add(acc).add(view[3usize]);
        acc = acc.add(acc).add(view[2usize]);
        acc = acc.add(acc).add(view[1usize]);
        acc = acc.add(acc).add(view[0usize]);
        acc
    }
    #[inline(always)]
    fn empty_root(level: usize) -> Digest {
        let words = constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level];
        [M31(words[0]), M31(words[1]), M31(words[2]), M31(words[3]),
                M31(words[4]), M31(words[5]), M31(words[6]), M31(words[7])]
    }
    fn validate_transition(public: SemanticPublic)
        -> Result<(), PoolV1PairForestSemanticTerminalErrorV1> {
        let source = public.transition.live_snapshot;
        let after = public.transition.candidate_afterstate;
        if source.pool != public.pool ||
                            source.deployment_domain != public.deployment_domain ||
                        source.sequence != source.next_pair_index ||
                    source.next_pair_index >= POOL_V1_PAIR_CAPACITY ||
                checked_next227(source.next_pair_index, after.next_pair_index)
            {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
        }
        let index = source.next_pair_index;
        let carry = bounded_append_carry(index);
        let mut level_index = 0usize;
        while level_index < 20 {
            let level = level_index;
            level_index += 1;
            if level == carry && carry < 20 { continue; }
            let expected =
                if level < carry || ((index >> level) & 1) == 0 {
                    empty_root(level)
                } else { digest227(source.frontier, level) };
            if digest227(after.next_frontier, level) != expected {
                return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
            }
        }
        Ok(())
    }
    fn poseidon_selectors(selectors: &Selectors)
        -> StateOnlyPoseidonSelectors {
        StateOnlyPoseidonSelectors {
            block: sum_interval227(selectors.high, QM31::ZERO, 0, 57),
            local: selectors.low,
        }
    }
    #[inline(never)]
    fn initial_variant_selectors(variant: CompiledVariant, high27: QM31,
        high28: QM31, high29: QM31) -> (QM31, QM31, QM31, QM31) {
        match variant {
            CompiledVariant::PrivateTransfer =>
                (high27, QM31::ZERO, high27.add(high28), high29),
            CompiledVariant::Withdrawal =>
                (QM31::ZERO, high27.add(high28).add(high29), QM31::ZERO,
                    QM31::ZERO),
        }
    }
    fn semantic_initial_and_absorption(public: SemanticPublic,
        openings: StateOnlyPoseidonOpenings, selectors: Selectors)
        -> ([QM31; 16], [QM31; 16]) {
        let nodes =
            sum_interval227(selectors.high,
                sum_interval227(selectors.high, QM31::ZERO, 4, 25), 33, 57);
        let first_common =
            selectors.high[0].add(selectors.high[1]).add(selectors.high[25]).add(selectors.high[30]);
        let (transfer_first, fixed, private_chunk_eight, private_chunk_two) =
            initial_variant_selectors(public.variant, selectors.high[27],
                selectors.high[28], selectors.high[29]);
        let full_initial_selector =
            selectors.low[0].mul(first_common.add(transfer_first).add(fixed));
        let rate_initial_selector = selectors.low[0].mul(nodes);
        let full = PreparedQm31Multiplier::new(full_initial_selector);
        let full_or_rate =
            PreparedQm31Multiplier::new(full_initial_selector.add(rate_initial_selector));
        let mut initial =
            {
                let mut output = [QM31::ZERO; 16];
                {
                    let lane = 0usize;
                    output[0] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 1usize;
                    output[1] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 2usize;
                    output[2] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 3usize;
                    output[3] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 4usize;
                    output[4] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 5usize;
                    output[5] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 6usize;
                    output[6] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 7usize;
                    output[7] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 8usize;
                    output[8] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 9usize;
                    output[9] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 10usize;
                    output[10] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 11usize;
                    output[11] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 12usize;
                    output[12] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 13usize;
                    output[13] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 14usize;
                    output[14] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                {
                    let lane = 15usize;
                    output[15] =
                        {
                            initial_lane227(lane, full_or_rate, full,
                                read227(openings.z, lane))
                        };
                }
                output
            };
        let note_first =
            selectors.high[1].add(selectors.high[30]).add(transfer_first);
        let domain =
            selectors.high[0].mul_m31(DOMAIN_OWNER_KEY).add(note_first.mul_m31(DOMAIN_NOTE)).add(selectors.high[25].mul_m31(DOMAIN_NULLIFIER));
        let length =
            selectors.high[0].mul_m31(M31(8)).add(note_first.mul_m31(M31(18))).add(selectors.high[25].mul_m31(M31(16)));
        initial[RATE] = initial[RATE].sub(selectors.low[0].mul(domain));
        initial[RATE + 1] =
            initial[RATE + 1].sub(selectors.low[0].mul(length));
        let mut chunk_eight =
            selectors.high[0].add(selectors.high[1]).add(selectors.high[2]).add(selectors.high[25]).add(selectors.high[26]).add(selectors.high[30]).add(selectors.high[31]);
        let mut chunk_two = selectors.high[3].add(selectors.high[32]);
        chunk_eight = chunk_eight.add(private_chunk_eight);
        chunk_two = chunk_two.add(private_chunk_two);
        let absorption =
            absorption_lanes_literal(selectors.low[12], fixed, chunk_two,
                chunk_eight, nodes, &openings.z);
        (initial, absorption)
    }
    fn absorption_lanes_literal(low: QM31, fixed: QM31, chunk_two: QM31,
        chunk_eight: QM31, nodes: QM31, openings: &[QM31; 16]) -> [QM31; 16] {
        {
            let mut output = [QM31::ZERO; 16];
            {
                let lane = 0usize;
                output[0] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 1usize;
                output[1] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 2usize;
                output[2] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 3usize;
                output[3] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 4usize;
                output[4] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 5usize;
                output[5] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 6usize;
                output[6] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 7usize;
                output[7] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 8usize;
                output[8] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 9usize;
                output[9] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 10usize;
                output[10] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 11usize;
                output[11] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 12usize;
                output[12] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 13usize;
                output[13] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 14usize;
                output[14] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            {
                let lane = 15usize;
                output[15] =
                    {
                        absorption_lane227(lane, low, fixed, chunk_two, chunk_eight,
                            nodes, read227(*openings, lane))
                    };
            }
            output
        }
    }
    #[inline(always)]
    fn add_digest_binding(mut output: [QM31; DIGEST_ELEMS], selector: QM31,
        opened: [QM31; POSEIDON2_WIDTH], start: usize, expected: Digest,
        right_tweak: bool) -> [QM31; DIGEST_ELEMS] {
        let mut lane_index = 0usize;
        let target = tweak227(expected[0usize], right_tweak, 0usize);
        output[0usize] =
            output[0usize].add(selector.mul(opened[start +
                                0usize].sub(lift_m31(target))));
        let target = tweak227(expected[1usize], right_tweak, 1usize);
        output[1usize] =
            output[1usize].add(selector.mul(opened[start +
                                1usize].sub(lift_m31(target))));
        let target = tweak227(expected[2usize], right_tweak, 2usize);
        output[2usize] =
            output[2usize].add(selector.mul(opened[start +
                                2usize].sub(lift_m31(target))));
        let target = tweak227(expected[3usize], right_tweak, 3usize);
        output[3usize] =
            output[3usize].add(selector.mul(opened[start +
                                3usize].sub(lift_m31(target))));
        let target = tweak227(expected[4usize], right_tweak, 4usize);
        output[4usize] =
            output[4usize].add(selector.mul(opened[start +
                                4usize].sub(lift_m31(target))));
        let target = tweak227(expected[5usize], right_tweak, 5usize);
        output[5usize] =
            output[5usize].add(selector.mul(opened[start +
                                5usize].sub(lift_m31(target))));
        let target = tweak227(expected[6usize], right_tweak, 6usize);
        output[6usize] =
            output[6usize].add(selector.mul(opened[start +
                                6usize].sub(lift_m31(target))));
        let target = tweak227(expected[7usize], right_tweak, 7usize);
        output[7usize] =
            output[7usize].add(selector.mul(opened[start +
                                7usize].sub(lift_m31(target))));
        output
    }
    #[inline(never)]
    fn add_schedule_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        public: SemanticPublic, openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors) {
        let (initial, absorption) =
            semantic_initial_and_absorption(public, *openings, *selectors);
        add_preweighted(packed, 0, &initial);
        add_preweighted(packed, 16, &absorption);
    }
    #[inline(never)]
    fn add_path_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors) {
        let path_selector =
            sum_interval227(selectors.high, QM31::ZERO, 57,
                    63).mul(selectors.low[1].add(selectors.low[5]).add(selectors.low[9]).add(selectors.low[13]));
        let path = path_lanes_literal(path_selector, openings);
        add_preweighted(packed, 32, &path);
    }
    fn path_lanes_literal(path_selector: QM31,
        openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
        let bit = openings.z[0];
        let mut path = [QM31::ZERO; 17];
        path[0] = path_selector.mul(bit.mul(bit.sub(QM31::ONE)));
        let mut lane_index = 0usize;
        let current = openings.z[1 + 0usize];
        path[1 + 0usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[0usize].sub(current));
        path[1 + DIGEST_ELEMS + 0usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            0usize].sub(current));
        let current = openings.z[1 + 1usize];
        path[1 + 1usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[1usize].sub(current));
        path[1 + DIGEST_ELEMS + 1usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            1usize].sub(current));
        let current = openings.z[1 + 2usize];
        path[1 + 2usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[2usize].sub(current));
        path[1 + DIGEST_ELEMS + 2usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            2usize].sub(current));
        let current = openings.z[1 + 3usize];
        path[1 + 3usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[3usize].sub(current));
        path[1 + DIGEST_ELEMS + 3usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            3usize].sub(current));
        let current = openings.z[1 + 4usize];
        path[1 + 4usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[4usize].sub(current));
        path[1 + DIGEST_ELEMS + 4usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            4usize].sub(current));
        let current = openings.z[1 + 5usize];
        path[1 + 5usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[5usize].sub(current));
        path[1 + DIGEST_ELEMS + 5usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            5usize].sub(current));
        let current = openings.z[1 + 6usize];
        path[1 + 6usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[6usize].sub(current));
        path[1 + DIGEST_ELEMS + 6usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            6usize].sub(current));
        let current = openings.z[1 + 7usize];
        path[1 + 7usize] =
            path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[7usize].sub(current));
        path[1 + DIGEST_ELEMS + 7usize] =
            path_selector.mul(bit).mul(openings.succ_z[RATE +
                            7usize].sub(current));
        path
    }
    #[inline(never)]
    fn add_value_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors) {
        let value_selectors =
            [selectors.row(16 * VALUE_AUXILIARY_BLOCK),
                    selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2),
                    selectors.row(16 * VALUE_AUXILIARY_BLOCK + 4)];
        let range_selector =
            QM31::ZERO.add(value_selectors[0]).add(value_selectors[1]).add(value_selectors[2]);
        let mut range = [QM31::ZERO; 33];
        let mut index = 0usize;
        range[0usize] =
            read227(openings.z,
                        0usize).square().sub(read227(openings.z, 0usize));
        range[1usize] =
            read227(openings.z,
                        1usize).square().sub(read227(openings.z, 1usize));
        range[2usize] =
            read227(openings.z,
                        2usize).square().sub(read227(openings.z, 2usize));
        range[3usize] =
            read227(openings.z,
                        3usize).square().sub(read227(openings.z, 3usize));
        range[4usize] =
            read227(openings.z,
                        4usize).square().sub(read227(openings.z, 4usize));
        range[5usize] =
            read227(openings.z,
                        5usize).square().sub(read227(openings.z, 5usize));
        range[6usize] =
            read227(openings.z,
                        6usize).square().sub(read227(openings.z, 6usize));
        range[7usize] =
            read227(openings.z,
                        7usize).square().sub(read227(openings.z, 7usize));
        range[8usize] =
            read227(openings.z,
                        8usize).square().sub(read227(openings.z, 8usize));
        range[9usize] =
            read227(openings.z,
                        9usize).square().sub(read227(openings.z, 9usize));
        index = 0;
        range[10 + 0usize] =
            read227(openings.succ_z,
                        0usize).square().sub(read227(openings.succ_z, 0usize));
        range[10 + 1usize] =
            read227(openings.succ_z,
                        1usize).square().sub(read227(openings.succ_z, 1usize));
        range[10 + 2usize] =
            read227(openings.succ_z,
                        2usize).square().sub(read227(openings.succ_z, 2usize));
        range[10 + 3usize] =
            read227(openings.succ_z,
                        3usize).square().sub(read227(openings.succ_z, 3usize));
        range[10 + 4usize] =
            read227(openings.succ_z,
                        4usize).square().sub(read227(openings.succ_z, 4usize));
        range[10 + 5usize] =
            read227(openings.succ_z,
                        5usize).square().sub(read227(openings.succ_z, 5usize));
        range[10 + 6usize] =
            read227(openings.succ_z,
                        6usize).square().sub(read227(openings.succ_z, 6usize));
        range[10 + 7usize] =
            read227(openings.succ_z,
                        7usize).square().sub(read227(openings.succ_z, 7usize));
        range[10 + 8usize] =
            read227(openings.succ_z,
                        8usize).square().sub(read227(openings.succ_z, 8usize));
        range[10 + 9usize] =
            read227(openings.succ_z,
                        9usize).square().sub(read227(openings.succ_z, 9usize));
        index = 0;
        range[20 + 0usize] =
            read227(openings.xor12_z,
                        0usize).square().sub(read227(openings.xor12_z, 0usize));
        range[20 + 1usize] =
            read227(openings.xor12_z,
                        1usize).square().sub(read227(openings.xor12_z, 1usize));
        range[20 + 2usize] =
            read227(openings.xor12_z,
                        2usize).square().sub(read227(openings.xor12_z, 2usize));
        range[20 + 3usize] =
            read227(openings.xor12_z,
                        3usize).square().sub(read227(openings.xor12_z, 3usize));
        range[20 + 4usize] =
            read227(openings.xor12_z,
                        4usize).square().sub(read227(openings.xor12_z, 4usize));
        range[20 + 5usize] =
            read227(openings.xor12_z,
                        5usize).square().sub(read227(openings.xor12_z, 5usize));
        range[20 + 6usize] =
            read227(openings.xor12_z,
                        6usize).square().sub(read227(openings.xor12_z, 6usize));
        range[20 + 7usize] =
            read227(openings.xor12_z,
                        7usize).square().sub(read227(openings.xor12_z, 7usize));
        range[20 + 8usize] =
            read227(openings.xor12_z,
                        8usize).square().sub(read227(openings.xor12_z, 8usize));
        range[20 + 9usize] =
            read227(openings.xor12_z,
                        9usize).square().sub(read227(openings.xor12_z, 9usize));
        let reconstructed =
            reconstruct_10(&openings.z).add(reconstruct_10(&openings.succ_z).mul_m31(M31(1
                                <<
                                10))).add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 <<
                            20)));
        range[30] = openings.z[10].sub(reconstructed);
        range[31] = openings.succ_z[10];
        range[32] = openings.xor12_z[10];
        {
            let mut residual_index = 0usize;
            range[0usize] = range_selector.mul(read227(range, 0usize));
            range[1usize] = range_selector.mul(read227(range, 1usize));
            range[2usize] = range_selector.mul(read227(range, 2usize));
            range[3usize] = range_selector.mul(read227(range, 3usize));
            range[4usize] = range_selector.mul(read227(range, 4usize));
            range[5usize] = range_selector.mul(read227(range, 5usize));
            range[6usize] = range_selector.mul(read227(range, 6usize));
            range[7usize] = range_selector.mul(read227(range, 7usize));
            range[8usize] = range_selector.mul(read227(range, 8usize));
            range[9usize] = range_selector.mul(read227(range, 9usize));
            range[10usize] = range_selector.mul(read227(range, 10usize));
            range[11usize] = range_selector.mul(read227(range, 11usize));
            range[12usize] = range_selector.mul(read227(range, 12usize));
            range[13usize] = range_selector.mul(read227(range, 13usize));
            range[14usize] = range_selector.mul(read227(range, 14usize));
            range[15usize] = range_selector.mul(read227(range, 15usize));
            range[16usize] = range_selector.mul(read227(range, 16usize));
            range[17usize] = range_selector.mul(read227(range, 17usize));
            range[18usize] = range_selector.mul(read227(range, 18usize));
            range[19usize] = range_selector.mul(read227(range, 19usize));
            range[20usize] = range_selector.mul(read227(range, 20usize));
            range[21usize] = range_selector.mul(read227(range, 21usize));
            range[22usize] = range_selector.mul(read227(range, 22usize));
            range[23usize] = range_selector.mul(read227(range, 23usize));
            range[24usize] = range_selector.mul(read227(range, 24usize));
            range[25usize] = range_selector.mul(read227(range, 25usize));
            range[26usize] = range_selector.mul(read227(range, 26usize));
            range[27usize] = range_selector.mul(read227(range, 27usize));
            range[28usize] = range_selector.mul(read227(range, 28usize));
            range[29usize] = range_selector.mul(read227(range, 29usize));
            range[30usize] = range_selector.mul(read227(range, 30usize));
            range[31usize] = range_selector.mul(read227(range, 31usize));
            range[32usize] = range_selector.mul(read227(range, 32usize));
            add_preweighted(packed, 49, &range);
        }
        let conservation_selector =
            selectors.row(16 * VALUE_AUXILIARY_BLOCK + 6);
        let conservation =
            [conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
                    conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1]))];
        add_preweighted(packed, 82, &conservation);
    }
    #[inline(never)]
    fn variant_expected_output(variant: CompiledVariant) -> M31 {
        match variant {
            CompiledVariant::PrivateTransfer => M31(1),
            CompiledVariant::Withdrawal => M31(0),
        }
    }
    #[inline(never)]
    fn add_occupancy_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        public: SemanticPublic, openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors) {
        let input_occupancy = selectors.row(INPUT_OCCUPANCY_ROW);
        let output_occupancy = selectors.row(OUTPUT_OCCUPANCY_ROW);
        let expected_output = variant_expected_output(public.variant);
        let occupancy =
            occupancy_lanes_literal(input_occupancy, output_occupancy,
                expected_output, &openings.z);
        add_preweighted(packed, 0, &occupancy);
    }
    fn occupancy_lanes_literal(input_occupancy: QM31, output_occupancy: QM31,
        expected_output: M31, opened: &[QM31; 16]) -> [QM31; 12] {
        let occupied = opened[0];
        let inverse = opened[1];
        let one_minus = QM31::ONE.sub(occupied);
        let mut occupancy = [QM31::ZERO; 12];
        let both = input_occupancy.add(output_occupancy);
        occupancy[0] = both.mul(occupied.mul(occupied.sub(QM31::ONE)));
        occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
        occupancy[2] = both.mul(one_minus.mul(inverse));
        let mut lane_index = 0usize;
        occupancy[3 + 0usize] = both.mul(one_minus.mul(opened[2 + 0usize]));
        occupancy[3 + 1usize] = both.mul(one_minus.mul(opened[2 + 1usize]));
        occupancy[3 + 2usize] = both.mul(one_minus.mul(opened[2 + 2usize]));
        occupancy[3 + 3usize] = both.mul(one_minus.mul(opened[2 + 3usize]));
        occupancy[3 + 4usize] = both.mul(one_minus.mul(opened[2 + 4usize]));
        occupancy[3 + 5usize] = both.mul(one_minus.mul(opened[2 + 5usize]));
        occupancy[3 + 6usize] = both.mul(one_minus.mul(opened[2 + 6usize]));
        occupancy[3 + 7usize] = both.mul(one_minus.mul(opened[2 + 7usize]));
        occupancy[11] =
            input_occupancy.mul(opened[10].mul(one_minus)).add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
        occupancy
    }
    #[inline(never)]
    fn public_digest_lanes(public: SemanticPublic,
        openings: StateOnlyPoseidonOpenings, selectors: Selectors)
        -> [QM31; DIGEST_ELEMS] {
        let mut digests = [QM31::ZERO; DIGEST_ELEMS];
        digests =
            add_digest_binding(digests, selectors.row(56 * 16 + 11),
                openings.z, 0, public.anchor, false);
        digests =
            add_digest_binding(digests, selectors.row(26 * 16 + 11),
                openings.z, 0, public.nullifier, false);
        if let Some(recipient) = public.recipient {
            digests =
                add_digest_binding(digests, selectors.row(29 * 16 + 11),
                    openings.z, 0, recipient, false);
        }
        digests =
            add_digest_binding(digests, selectors.row(32 * 16 + 11),
                openings.z, 0, public.change, false);
        let source = public.transition.live_snapshot;
        let after = public.transition.candidate_afterstate;
        let mut level_index = 0usize;
        let block = 34 + 0usize;
        if ((source.next_pair_index >> 0usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(0usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 0usize), false);
        }
        let block = 34 + 1usize;
        if ((source.next_pair_index >> 1usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(1usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 1usize), false);
        }
        let block = 34 + 2usize;
        if ((source.next_pair_index >> 2usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(2usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 2usize), false);
        }
        let block = 34 + 3usize;
        if ((source.next_pair_index >> 3usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(3usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 3usize), false);
        }
        let block = 34 + 4usize;
        if ((source.next_pair_index >> 4usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(4usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 4usize), false);
        }
        let block = 34 + 5usize;
        if ((source.next_pair_index >> 5usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(5usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 5usize), false);
        }
        let block = 34 + 6usize;
        if ((source.next_pair_index >> 6usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(6usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 6usize), false);
        }
        let block = 34 + 7usize;
        if ((source.next_pair_index >> 7usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(7usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 7usize), false);
        }
        let block = 34 + 8usize;
        if ((source.next_pair_index >> 8usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(8usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 8usize), false);
        }
        let block = 34 + 9usize;
        if ((source.next_pair_index >> 9usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(9usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 9usize), false);
        }
        let block = 34 + 10usize;
        if ((source.next_pair_index >> 10usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(10usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 10usize), false);
        }
        let block = 34 + 11usize;
        if ((source.next_pair_index >> 11usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(11usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 11usize), false);
        }
        let block = 34 + 12usize;
        if ((source.next_pair_index >> 12usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(12usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 12usize), false);
        }
        let block = 34 + 13usize;
        if ((source.next_pair_index >> 13usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(13usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 13usize), false);
        }
        let block = 34 + 14usize;
        if ((source.next_pair_index >> 14usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(14usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 14usize), false);
        }
        let block = 34 + 15usize;
        if ((source.next_pair_index >> 15usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(15usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 15usize), false);
        }
        let block = 34 + 16usize;
        if ((source.next_pair_index >> 16usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(16usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 16usize), false);
        }
        let block = 34 + 17usize;
        if ((source.next_pair_index >> 17usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(17usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 17usize), false);
        }
        let block = 34 + 18usize;
        if ((source.next_pair_index >> 18usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(18usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 18usize), false);
        }
        let block = 34 + 19usize;
        if ((source.next_pair_index >> 19usize) & 1) == 0 {
            digests =
                add_digest_binding(digests, selectors.row(block * 16),
                    openings.z, RATE, empty_root(19usize), true);
        } else {
            digests =
                add_digest_binding(digests, selectors.row(block * 16 + 12),
                    openings.z, 0, digest227(source.frontier, 19usize), false);
        }
        digests =
            add_digest_binding(digests, selectors.row(53 * 16 + 11),
                openings.z, 0, after.next_root, false);
        let carry = bounded_append_carry(source.next_pair_index);
        if carry < 20 {
            digests =
                add_digest_binding(digests,
                    selectors.row((33 + carry) * 16 + 11), openings.z, 0,
                    after.next_frontier[carry], false);
        }
        digests
    }
    #[inline(never)]
    fn scalar_lanes(variant: CompiledVariant, withdrawal_amount_present: bool,
        input_asset: QM31, mut output_scalar: QM31,
        private_transfer_term: QM31, withdrawal_term: QM31) -> [QM31; 2] {
        match variant {
            CompiledVariant::PrivateTransfer => {
                output_scalar = output_scalar.add(private_transfer_term);
            }
            CompiledVariant::Withdrawal => {
                if withdrawal_amount_present {
                    output_scalar = output_scalar.add(withdrawal_term);
                }
            }
        }
        [input_asset, output_scalar]
    }
    fn semantic_packed(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1] {
        let mut packed =
            [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
        add_schedule_lanes(&mut packed, public, openings, selectors);
        add_path_lanes(&mut packed, openings, selectors);
        add_value_lanes(&mut packed, openings, selectors);
        add_occupancy_lanes(&mut packed, public, openings, selectors);
        add_preweighted(&mut packed, 84,
            &public_digest_lanes(public, *openings, *selectors));
        let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
        let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
        let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
        let private_transfer_term =
            selectors.row(28 * 16 + 12).mul(asset_difference);
        let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
        let withdrawal_term =
            selectors.row(16 * VALUE_AUXILIARY_BLOCK +
                        2).mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
        let scalars =
            scalar_lanes(public.variant, public.withdrawal_amount.is_some(),
                input_asset, output_scalar, private_transfer_term,
                withdrawal_term);
        add_preweighted(&mut packed, 92, &scalars);
        packed
    }
    fn selected_claim(claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: usize, column: usize) -> QM31 {
        claims[point * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 +
                column]
    }
    #[inline(never)]
    fn copy_variant(variant: CompiledVariant)
        -> PoolV1PairForestCompiledVariantV1 {
        match variant {
            CompiledVariant::PrivateTransfer =>
                PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            CompiledVariant::Withdrawal =>
                PoolV1PairForestCompiledVariantV1::Withdrawal,
        }
    }
    fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
        let mut product = equality_factor(left[0], right[0]);
        product = product.mul(equality_factor(left[1], right[1]));
        product = product.mul(equality_factor(left[2], right[2]));
        product = product.mul(equality_factor(left[3], right[3]));
        product = product.mul(equality_factor(left[4], right[4]));
        product = product.mul(equality_factor(left[5], right[5]));
        product = product.mul(equality_factor(left[6], right[6]));
        product = product.mul(equality_factor(left[7], right[7]));
        product = product.mul(equality_factor(left[8], right[8]));
        product = product.mul(equality_factor(left[9], right[9]));
        product
    }
    #[allow(clippy::type_complexity)]
    fn composition_parts(public: SemanticPublic,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        ->
            Result<(QM31, [QM31; 16],
            [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], QM31, QM31, QM31),
            PoolV1PairForestSemanticTerminalErrorV1> {
        let invalid_amount =
            match public.withdrawal_amount {
                None => false,
                Some(amount) => amount == 0 || amount >= (1 << 30u32),
            };
        if invalid_amount {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
        }
        validate_transition(public)?;
        let openings =
            StateOnlyPoseidonOpenings {
                z: select_c1_227(*claims, 0),
                succ_z: select_c1_227(*claims, 1),
                xor12_z: select_c1_227(*claims, 2),
            };
        let mask_only =
            {
                let mut output =
                    [QM31::ZERO; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS];
                let mut column = 0usize;
                while column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
                    output[column] =
                        {
                            selected_claim(claims, 0,
                                POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column)
                        };
                    column += 1;
                }
                output
            };
        let selectors = Selectors::boxed_at_point(point);
        let poseidon =
            evaluate_state_only_poseidon_oracle_projected(&openings,
                &poseidon_selectors(&selectors));
        let semantic = semantic_packed(public, &openings, &selectors);
        let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
        let copy =
            evaluate_with_selectors(&openings.z, h1_z, &selectors, lambda,
                chi, public.transition.live_snapshot.next_pair_index,
                copy_variant(public.variant));
        let prepared_theta = PreparedQm31Multiplier::new(theta);
        let mut composition = copy.residual;
        let mut index = semantic.len();
        while index > 0 {
            index -= 1;
            composition =
                prepared_theta.mul(composition).add(read227(semantic, index));
        }
        index = poseidon.len();
        while index > 0 {
            index -= 1;
            composition =
                prepared_theta.mul(composition).add(read227(poseidon, index));
        }
        Ok((composition, openings.z, mask_only,
                selected_claim(claims, 0, SELECTED_G_COLUMN), h1_z,
                copy.active))
    }
    fn terminal_parts(public: SemanticPublic,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        ->
            Result<(QM31, [QM31; 16],
            [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], QM31),
            PoolV1PairForestSemanticTerminalErrorV1> {
        let (composition, c1, mask_only, g, h1_z, copy_active) =
            composition_parts(public, claims, point, lambda, chi, theta)?;
        let original =
            equality_value(zerocheck_point,
                            point).mul(composition).add(mu.mul(h1_z)).add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
        Ok((original, c1, mask_only, g))
    }
    fn private_public<'a>(public: &PoolV1PrivateTransferPublicV1,
        transition: &'a PoolV1PairLatePublicStatementV1) -> SemanticPublic {
        SemanticPublic {
            variant: CompiledVariant::PrivateTransfer,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: Some(public.recipient_commitment),
            change: public.change_commitment,
            withdrawal_amount: None,
            transition: *transition,
        }
    }
    fn withdrawal_public<'a>(public: &PoolV1WithdrawalPublicV1,
        transition: &'a PoolV1PairLatePublicStatementV1) -> SemanticPublic {
        SemanticPublic {
            variant: CompiledVariant::Withdrawal,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: None,
            change: public.change_commitment,
            withdrawal_amount: Some(public.amount),
            transition: *transition,
        }
    }
    macro_rules! define_variant_terminal {
        ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty,
        $convert:ident) =>
        {
            #[allow(clippy::too_many_arguments)] pub fn
            $composition(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,) ->
            Result<QM31, PoolV1PairForestSemanticTerminalErrorV1>
            {
                Ok(composition_parts($convert(public, transition), claims,
                point, lambda, chi, theta,)? .0)
            } #[allow(clippy::too_many_arguments)] pub fn
            $unmasked(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
            zerocheck_point: &[QM31; 10], mu: QM31,) -> Result<QM31,
            PoolV1PairForestSemanticTerminalErrorV1>
            {
                Ok(terminal_parts($convert(public, transition), claims, point,
                lambda, chi, theta, zerocheck_point, mu,)? .0)
            } #[allow(clippy::too_many_arguments)] #[inline(never)] pub fn
            $masked(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
            zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31,) ->
            Result<QM31, PoolV1PairForestSemanticTerminalErrorV1>
            {
                let (original, c1, mask_only, g) =
                terminal_parts($convert(public, transition), claims, point,
                lambda, chi, theta, zerocheck_point, mu,)?;
                Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                point).add(eta.mul(original)))
            }
        };
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(composition_parts(private_public(public, transition), claims,
                        point, lambda, chi, theta)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(terminal_parts(private_public(public, transition), claims, point,
                        lambda, chi, theta, zerocheck_point, mu)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    #[inline(never)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        let (original, c1, mask_only, g) =
            terminal_parts(private_public(public, transition), claims, point,
                    lambda, chi, theta, zerocheck_point, mu)?;
        Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                    point).add(eta.mul(original)))
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(composition_parts(withdrawal_public(public, transition), claims,
                        point, lambda, chi, theta)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(terminal_parts(withdrawal_public(public, transition), claims,
                        point, lambda, chi, theta, zerocheck_point, mu)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    #[inline(never)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        let (original, c1, mask_only, g) =
            terminal_parts(withdrawal_public(public, transition), claims,
                    point, lambda, chi, theta, zerocheck_point, mu)?;
        Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                    point).add(eta.mul(original)))
    }
    /// R0's width-29 view of this exact pair-forest terminal. No generic Spend
    /// terminal, legacy transcript or legacy claim stride is selected here.
    pub mod r0 {
        use super::*;
        use alloc::vec::Vec;
        use aspis_core::field::WideExact;
        use aspis_core::state_only_prefix::r0::{
            Challenges, Error, PointClaims,
        };
        pub enum Public<'a> {
            Transfer(&'a PoolV1PrivateTransferPublicV1,
                &'a PoolV1PairLatePublicStatementV1),
            Withdrawal(&'a PoolV1WithdrawalPublicV1,
                &'a PoolV1PairLatePublicStatementV1),
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl<'a> ::core::clone::TrivialClone for Public<'a> { }
        #[automatically_derived]
        impl<'a> ::core::clone::Clone for Public<'a> {
            #[inline]
            fn clone(&self) -> Public<'a> {
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PrivateTransferPublicV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PairLatePublicStatementV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1WithdrawalPublicV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PairLatePublicStatementV1>;
                *self
            }
        }
        #[automatically_derived]
        impl<'a> ::core::marker::Copy for Public<'a> { }
        impl<'a> Public<'a> {
            pub(super) fn semantic(self) -> SemanticPublic {
                match self {
                    Self::Transfer(public, transition) =>
                        private_public(public, transition),
                    Self::Withdrawal(public, transition) =>
                        withdrawal_public(public, transition),
                }
            }
            pub fn transition(self) -> &'a PoolV1PairLatePublicStatementV1 {
                match self {
                    Self::Transfer(_, t) | Self::Withdrawal(_, t) => t,
                }
            }
            /// SPEC §9 declaration order. Pool/domain/sequence and source current
            /// root are not fields of R0P.Public and are not silently hashed here.
            /// Existing reject-only public guards remain in the terminal.
            pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
                fn fields(out: &mut Vec<u8>, values: &[M31])
                    -> Result<(), Error> {
                    for value in values {
                        if value.0 >= aspis_core::field::P {
                            return Err(Error::Public);
                        }
                        out.extend_from_slice(&value.0.to_le_bytes());
                    }
                    Ok(())
                }
                fn frontier(out: &mut Vec<u8>, values: &[Digest; 20])
                    -> Result<(), Error> {
                    fields(out, &values[0])?;
                    fields(out, &values[1])?;
                    fields(out, &values[2])?;
                    fields(out, &values[3])?;
                    fields(out, &values[4])?;
                    fields(out, &values[5])?;
                    fields(out, &values[6])?;
                    fields(out, &values[7])?;
                    fields(out, &values[8])?;
                    fields(out, &values[9])?;
                    fields(out, &values[10])?;
                    fields(out, &values[11])?;
                    fields(out, &values[12])?;
                    fields(out, &values[13])?;
                    fields(out, &values[14])?;
                    fields(out, &values[15])?;
                    fields(out, &values[16])?;
                    fields(out, &values[17])?;
                    fields(out, &values[18])?;
                    fields(out, &values[19])?;
                    Ok(())
                }
                let p = self.semantic();
                let mut out = Vec::new();
                out.push(match p.variant {
                        CompiledVariant::PrivateTransfer => 0,
                        CompiledVariant::Withdrawal => 1,
                    });
                fields(&mut out, &p.anchor)?;
                fields(&mut out, &p.nullifier)?;
                fields(&mut out, &[p.asset_id])?;
                out.push(u8::from(p.recipient.is_some()));
                if let Some(value) = p.recipient {
                    fields(&mut out, &value)?;
                }
                fields(&mut out, &p.change)?;
                out.push(u8::from(p.withdrawal_amount.is_some()));
                if let Some(value) = p.withdrawal_amount {
                    fields(&mut out, &[M31(value)])?;
                }
                let source = p.transition.live_snapshot;
                let after = p.transition.candidate_afterstate;
                out.extend_from_slice(&source.next_pair_index.to_le_bytes());
                frontier(&mut out, &source.frontier)?;
                fields(&mut out, &after.next_root)?;
                frontier(&mut out, &after.next_frontier)?;
                Ok(out)
            }
            /// Fast K path. D is deliberately absent from the terminal formula,
            /// but its three claims remain in the width-29 opening statement.
            pub fn terminal_qm31(self, claims: &[[QM31; 29]; 3],
                alpha: &[QM31; 10], c: &Challenges) -> Result<QM31, Error> {
                let mut selected = [QM31::ZERO; 84];
                let mut i = 0usize;
                while i < 84 { selected[i] = claims[i / 28][i % 28]; i += 1; }
                match terminal_parts(self.semantic(), &selected, alpha,
                        c.lambda, c.chi, c.theta, &c.zc, c.mu) {
                    Ok(parts) => Ok(parts.0),
                    Err(_) => Err(Error::Public),
                }
            }
            /// Extend the existing polynomial evaluator to E without narrowing
            /// adversarial E claims. At fixed K coordinates, substituting
            /// c0+t*c1 for every claim gives degree <=25: the Poseidon evaluator
            /// has two consecutive fifth powers (5*5); Copy has four affine
            /// denominators times H1 (degree 5); the other families have degree
            /// <=3. Selectors, theta, mu and equality weights are constants here.
            /// Hence 26 K evaluations determine its value at t=v exactly.
            /// This is polynomial base extension, not a probabilistic identity
            /// test. The honest K path requires only one terminal evaluation.
            pub fn terminal(self, claims: &PointClaims, alpha: &[QM31; 10],
                c: &Challenges) -> Result<WideExact, Error> {
                if claims.iter().flatten().all(|x| x.c1() == QM31::ZERO) {
                    let values = terminal_values(claims, None);
                    return self.terminal_qm31(&values, alpha,
                                c).map(WideExact::from_qm31);
                }
                let mut total = WideExact::ZERO;
                for i in 0..26u32 {
                    let values = terminal_values(claims, Some(M31(i)));
                    let value = self.terminal_qm31(&values, alpha, c)?;
                    let mut numerator = WideExact::ONE;
                    let mut denominator = M31::ONE;
                    for j in 0..26u32 {
                        if i == j { continue; }
                        numerator =
                            numerator.mul(WideExact::V.sub(WideExact::from_qm31(lift_m31(M31(j)))));
                        denominator = denominator.mul(M31(i).sub(M31(j)));
                    }
                    total =
                        total.add(numerator.mul_qm31(value.mul_m31(denominator.inv())));
                }
                Ok(total)
            }
        }
        #[inline(never)]
        fn terminal_values(claims: &PointClaims, t: Option<M31>)
            -> [[QM31; 29]; 3] {
            let mut values = [[QM31::ZERO; 29]; 3];
            for p in 0..3 {
                for l in 0..29 {
                    let x = claims[p][l];
                    values[p][l] =
                        match t {
                            None => x.c0(),
                            Some(t) => x.c0().add(x.c1().mul_m31(t)),
                        };
                }
            }
            values
        }
    }
    #[inline(always)]
    fn equality_factor(a: QM31, b: QM31) -> QM31 {
        let ab = a.mul(b);
        QM31::ONE.sub(a).sub(b).add(ab).add(ab)
    }
    fn claim227(claims: [[QM31; 29]; 3], index: usize) -> QM31 {
        let row = claims[index / 28];
        row[index % 28]
    }
    /// Owned value entry: copy the immutable inputs before evaluating the same chain.
    pub fn reference227(public: SemanticPublic, claims: [[QM31; 29]; 3],
        alpha: [QM31; 10], c: aspis_core::state_only_prefix::r0::Challenges)
        -> Result<QM31, aspis_core::state_only_prefix::r0::Error> {
        let selected = select227(claims);
        match terminal_parts(public, &selected, &alpha, c.lambda, c.chi,
                c.theta, &c.zc, c.mu) {
            Ok(parts) => Ok(parts.0),
            Err(_) => Err(aspis_core::state_only_prefix::r0::Error::Public),
        }
    }
    fn read227<const N : usize>(values: [QM31; N], index: usize) -> QM31 {
        values[index]
    }
    fn digest227(values: [Digest; 20], index: usize) -> Digest {
        values[index]
    }
    fn sum_interval227(high: [QM31; 64], initial: QM31, start: usize,
        end: usize) -> QM31 {
        let mut sum = initial;
        let mut i = start;
        while i < end { sum = sum.add(read227(high, i)); i += 1; }
        sum
    }
    fn initial_lane227(lane: usize, full_or_rate: PreparedQm31Multiplier,
        full: PreparedQm31Multiplier, value: QM31) -> QM31 {
        if lane < RATE { full_or_rate.mul(value) } else { full.mul(value) }
    }
    fn tweak227(value: M31, right_tweak: bool, lane: usize) -> M31 {
        if right_tweak && lane + 1 == DIGEST_ELEMS {
            value.add(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else { value }
    }
    pub fn select227(claims: [[QM31; 29]; 3]) -> [QM31; 84] {
        let mut selected = [QM31::ZERO; 84];
        let mut i = 0usize;
        while i < 84 {
            let value = claim227(claims, i);
            selected[i] = value;
            i += 1;
        }
        selected
    }
    fn absorption_lane227(lane: usize, low: QM31, fixed: QM31,
        chunk_two: QM31, chunk_eight: QM31, nodes: QM31, opened: QM31)
        -> QM31 {
        let blocks =
            if lane < 2 {
                fixed
            } else if lane < RATE {
                fixed.add(chunk_two)
            } else { fixed.add(chunk_two).add(chunk_eight).add(nodes) };
        low.mul(blocks).mul(opened)
    }
    fn checked_next227(index: u64, next: u64) -> bool {
        match index.checked_add(1) {
            Some(value) => value != next,
            None => true,
        }
    }
    use crate::reference_poseidon::evaluate_state_only_poseidon_oracle_projected;
    pub fn native227(public: r0::Public<'_>, claims: &[[QM31; 29]; 3],
        alpha: &[QM31; 10], c: &aspis_core::state_only_prefix::r0::Challenges)
        -> Result<QM31, aspis_core::state_only_prefix::r0::Error> {
        reference227(public.semantic(), *claims, *alpha, *c)
    }
    #[inline(never)]
    fn select_c1_227(claims: [QM31; 84], row: usize) -> [QM31; 16] {
        [selected_claim(&claims, row, 0), selected_claim(&claims, row, 1),
                selected_claim(&claims, row, 2),
                selected_claim(&claims, row, 3),
                selected_claim(&claims, row, 4),
                selected_claim(&claims, row, 5),
                selected_claim(&claims, row, 6),
                selected_claim(&claims, row, 7),
                selected_claim(&claims, row, 8),
                selected_claim(&claims, row, 9),
                selected_claim(&claims, row, 10),
                selected_claim(&claims, row, 11),
                selected_claim(&claims, row, 12),
                selected_claim(&claims, row, 13),
                selected_claim(&claims, row, 14),
                selected_claim(&claims, row, 15)]
    }
}
/// Owned entry with identical argument and complete Result signature.
pub fn reference227(public: reference_terminal::r0::Public<'_>,
    claims: &[[aspis_core::field::QM31; 29]; 3],
    alpha: &[aspis_core::field::QM31; 10],
    c: &aspis_core::state_only_prefix::r0::Challenges)
    ->
        Result<aspis_core::field::QM31,
        aspis_core::state_only_prefix::r0::Error> {
    public.terminal_qm31(claims, alpha, c)
}
pub mod std194227 {
    //! Owned expressions of the differing reached Rust 1.94.1 conversion bodies.
    //! Source mapping: std227-comparison-construct-resume5.json.
    pub fn from_u32_u64(small: u32) -> u64 { small as u64 }
    pub fn from_bool_u32(small: bool) -> u32 { small as u8 as u32 }
    pub fn from_u16_usize(small: u16) -> usize { small as usize }
    pub fn from_u8_usize(small: u8) -> usize { small as usize }
}
mod reference_copy_terminal {
    //! Allocation-bounded SBF-safe Copy lane for the eight-lane Pool V1
    //! pair-forest relation.
    //!
    //! Runtime evaluation consumes only generated patterns, endpoints and fixed
    //! active-row masks. The allocation-heavy typed registry remains the
    //! independent host compiler/reference boundary and is not linked on SBF.
    macro_rules! qm31_array {
        ($n:expr, $index:ident, $body:expr) =>
        {{
                let mut output = [QM31::ZERO; $n]; let mut $index = 0usize;
                while $index < $n { output[$index] = $body; $index += 1; }
                output
            }};
    }
    use crate::host_terminal_field::PreparedQm31Multiplier;
    use aspis_core::field::{CM31, M31, QM31};
    use aspis_statement::poseidon2::POSEIDON2_WIDTH;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1: usize = 1024;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1: usize = 16;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1: usize = 136;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1: usize = 14;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1:
        usize =
        if false { 2 } else { 1 };
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize
        =
        core::mem::size_of::<Selectors>();
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1: usize =
        if false { 103 * core::mem::size_of::<QM31>() } else { 0 };
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_BYTES_V1: usize =
        POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1 +
            POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1;
    pub const
        PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1:
        u64 =
        constants::ACTIVE_ROWS_FINGERPRINT;
    /// Exact SBF-safe active-row schedule consumed by the selected verifier.
    /// Host generation tests independently replay it from the typed tuple registry.
    pub fn pool_v1_pair_forest_copy_active_row_masks_compiled_v1()
        -> &'static [u16; 64] {
        &constants::ACTIVE_ROW_MASKS
    }
    /// Frozen row-to-group schedule generated from the exact pair-forest copy
    /// registry.  The selected verifier consumes this directly instead of
    /// rebuilding and deduplicating public layout data on every transaction.
    pub fn pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1()
        -> &'static [u8; 64] {
        &constants::INACTIVE_ROW_GROUPS
    }
    /// Deduplicated inactive masks referenced by
    /// [`pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1`].
    pub fn pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()
        -> &'static [u16] {
        &constants::INACTIVE_GROUP_MASKS
    }
    const _: () =
        if !(POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1)
            {
            ::core::panicking::panic("assertion failed: POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1")
        };
    const _: () =
        if !(constants::COPY_LINKS.len() ==
                    POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1) {
            ::core::panicking::panic("assertion failed: constants::COPY_LINKS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1")
        };
    const _: () =
        if !(constants::COPY_PATTERNS.len() ==
                    POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1) {
            ::core::panicking::panic("assertion failed: constants::COPY_PATTERNS.len() ==\n    POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1")
        };
    const _: () =
        if !(constants::ACTIVE_ROW_MASKS.len() == 64) {
            ::core::panicking::panic("assertion failed: constants::ACTIVE_ROW_MASKS.len() == 64")
        };
    const _: () =
        if !(constants::INACTIVE_ROW_GROUPS.len() == 64) {
            ::core::panicking::panic("assertion failed: constants::INACTIVE_ROW_GROUPS.len() == 64")
        };
    const _: () =
        if !(constants::INACTIVE_GROUP_MASKS.len() <= 64) {
            ::core::panicking::panic("assertion failed: constants::INACTIVE_GROUP_MASKS.len() <= 64")
        };
    pub enum PoolV1PairForestCompiledVariantV1 {
        PrivateTransfer,
        Withdrawal,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestCompiledVariantV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestCompiledVariantV1 { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestCompiledVariantV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    PoolV1PairForestCompiledVariantV1::PrivateTransfer =>
                        "PrivateTransfer",
                    PoolV1PairForestCompiledVariantV1::Withdrawal =>
                        "Withdrawal",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestCompiledVariantV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestCompiledVariantV1) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub struct PoolV1PairForestCompiledCopyTerminalV1 {
        pub residual: QM31,
        pub active: QM31,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestCompiledCopyTerminalV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestCompiledCopyTerminalV1 {
            let _: ::core::clone::AssertParamIsClone<QM31>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestCompiledCopyTerminalV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(f,
                "PoolV1PairForestCompiledCopyTerminalV1", "residual",
                &self.residual, "active", &&self.active)
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestCompiledCopyTerminalV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestCompiledCopyTerminalV1) -> bool {
            self.residual == other.residual && self.active == other.active
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<QM31>;
        }
    }
    struct CompiledPoolV1PairForestPattern {
        /// 0 = zero, 1 = row-local C1 cell plus a canonical M31 offset.
        kinds: [u8; POSEIDON2_WIDTH],
        columns: [u8; POSEIDON2_WIDTH],
        offsets: [u32; POSEIDON2_WIDTH],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        CompiledPoolV1PairForestPattern {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestPattern {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestPattern {
            let _: ::core::clone::AssertParamIsClone<[u8; POSEIDON2_WIDTH]>;
            let _: ::core::clone::AssertParamIsClone<[u8; POSEIDON2_WIDTH]>;
            let _: ::core::clone::AssertParamIsClone<[u32; POSEIDON2_WIDTH]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestPattern { }
    struct CompiledPoolV1PairForestEndpoint {
        row: u16,
        slot: u8,
        pattern: u8,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        CompiledPoolV1PairForestEndpoint {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestEndpoint {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestEndpoint {
            let _: ::core::clone::AssertParamIsClone<u16>;
            let _: ::core::clone::AssertParamIsClone<u8>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestEndpoint { }
    struct CompiledPoolV1PairForestLink {
        tag: u32,
        /// 0 = one, 1 = transfer, 2 = withdrawal, 3 = append-left,
        /// 4 = append-right.
        weight_kind: u8,
        weight_level: u8,
        producer: CompiledPoolV1PairForestEndpoint,
        consumer: CompiledPoolV1PairForestEndpoint,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CompiledPoolV1PairForestLink {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestLink {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestLink {
            let _: ::core::clone::AssertParamIsClone<u32>;
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _:
                    ::core::clone::AssertParamIsClone<CompiledPoolV1PairForestEndpoint>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestLink { }
    mod constants {
        use super::{
            CompiledPoolV1PairForestEndpoint, CompiledPoolV1PairForestLink,
            CompiledPoolV1PairForestPattern,
        };
        pub(crate) const ACTIVE_ROWS_FINGERPRINT: u64 = 0xdf394a5a8554d09c;
        pub(crate) const ACTIVE_ROW_MASKS: [u16; 64] =
            [6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048,
                    6145, 2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214,
                    26214, 26214, 26214, 1749];
        pub(crate) const INACTIVE_ROW_GROUPS: [u8; 64] =
            [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                    1, 1, 1, 0, 2, 3, 1, 4, 3, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 5, 5, 5,
                    5, 6];
        pub(crate) const INACTIVE_GROUP_MASKS: [u16; 7] =
            [59391, 59390, 61438, 63487, 63486, 39321, 63786];
        pub(crate) const COPY_PATTERNS: [CompiledPoolV1PairForestPattern; 14]
            =
            [CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                        columns: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                                15],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0,
                                0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 1051521018, 0, 0, 0, 0, 0, 0,
                                0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0,
                                0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    }];
        pub(crate) const COPY_LINKS: [CompiledPoolV1PairForestLink; 136] =
            [CompiledPoolV1PairForestLink {
                        tag: 1124073472,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 27,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 32,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073473,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 43,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 48,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073474,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 411,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 416,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073475,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 443,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 448,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073476,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 459,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 464,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073477,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 491,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 496,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073478,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 507,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 512,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073479,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 11,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 28,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073480,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 12,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 412,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073481,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 44,
                            slot: 0,
                            pattern: 2,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 428,
                            slot: 0,
                            pattern: 3,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073482,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 60,
                            slot: 0,
                            pattern: 4,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 428,
                            slot: 1,
                            pattern: 5,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073483,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 44,
                            slot: 1,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1008,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073484,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 460,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1010,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073485,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 508,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1012,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073486,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1008,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 0,
                            pattern: 6,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073487,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1010,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 1,
                            pattern: 8,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073488,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1012,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1015,
                            slot: 0,
                            pattern: 8,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073489,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 0,
                            pattern: 9,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1015,
                            slot: 1,
                            pattern: 6,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073490,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 64,
                            slot: 0,
                            pattern: 10,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1017,
                            slot: 0,
                            pattern: 11,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073491,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 913,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1017,
                            slot: 1,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073492,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 523,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1018,
                            slot: 0,
                            pattern: 11,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073493,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 475,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 540,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073494,
                        weight_kind: 2,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 523,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 540,
                            slot: 1,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073495,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1018,
                            slot: 0,
                            pattern: 11,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 528,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073496,
                        weight_kind: 3,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 539,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 556,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073497,
                        weight_kind: 4,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 539,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 544,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073498,
                        weight_kind: 3,
                        weight_level: 1,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 555,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 572,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073499,
                        weight_kind: 4,
                        weight_level: 1,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 555,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 560,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073500,
                        weight_kind: 3,
                        weight_level: 2,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 571,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 588,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073501,
                        weight_kind: 4,
                        weight_level: 2,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 571,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 576,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073502,
                        weight_kind: 3,
                        weight_level: 3,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 587,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 604,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073503,
                        weight_kind: 4,
                        weight_level: 3,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 587,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 592,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073504,
                        weight_kind: 3,
                        weight_level: 4,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 603,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 620,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073505,
                        weight_kind: 4,
                        weight_level: 4,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 603,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 608,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073506,
                        weight_kind: 3,
                        weight_level: 5,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 619,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 636,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073507,
                        weight_kind: 4,
                        weight_level: 5,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 619,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 624,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073508,
                        weight_kind: 3,
                        weight_level: 6,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 635,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 652,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073509,
                        weight_kind: 4,
                        weight_level: 6,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 635,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 640,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073510,
                        weight_kind: 3,
                        weight_level: 7,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 651,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 668,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073511,
                        weight_kind: 4,
                        weight_level: 7,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 651,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 656,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073512,
                        weight_kind: 3,
                        weight_level: 8,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 667,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 684,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073513,
                        weight_kind: 4,
                        weight_level: 8,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 667,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 672,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073514,
                        weight_kind: 3,
                        weight_level: 9,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 683,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 700,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073515,
                        weight_kind: 4,
                        weight_level: 9,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 683,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 688,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073516,
                        weight_kind: 3,
                        weight_level: 10,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 699,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 716,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073517,
                        weight_kind: 4,
                        weight_level: 10,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 699,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 704,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073518,
                        weight_kind: 3,
                        weight_level: 11,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 715,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 732,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073519,
                        weight_kind: 4,
                        weight_level: 11,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 715,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 720,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073520,
                        weight_kind: 3,
                        weight_level: 12,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 731,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 748,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073521,
                        weight_kind: 4,
                        weight_level: 12,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 731,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 736,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073522,
                        weight_kind: 3,
                        weight_level: 13,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 747,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 764,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073523,
                        weight_kind: 4,
                        weight_level: 13,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 747,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 752,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073524,
                        weight_kind: 3,
                        weight_level: 14,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 763,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 780,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073525,
                        weight_kind: 4,
                        weight_level: 14,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 763,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 768,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073526,
                        weight_kind: 3,
                        weight_level: 15,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 779,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 796,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073527,
                        weight_kind: 4,
                        weight_level: 15,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 779,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 784,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073528,
                        weight_kind: 3,
                        weight_level: 16,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 795,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 812,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073529,
                        weight_kind: 4,
                        weight_level: 16,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 795,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 800,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073530,
                        weight_kind: 3,
                        weight_level: 17,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 811,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 828,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073531,
                        weight_kind: 4,
                        weight_level: 17,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 811,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 816,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073532,
                        weight_kind: 3,
                        weight_level: 18,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 827,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 844,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073533,
                        weight_kind: 4,
                        weight_level: 18,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 827,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 832,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073534,
                        weight_kind: 3,
                        weight_level: 19,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 843,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 860,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073535,
                        weight_kind: 4,
                        weight_level: 19,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 843,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 848,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073536,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 59,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 913,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073537,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 914,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 76,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073538,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 914,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 64,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073539,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 75,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 917,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073540,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 918,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 92,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073541,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 918,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 80,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073542,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 91,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 921,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073543,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 922,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 108,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073544,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 922,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 96,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073545,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 107,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 925,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073546,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 926,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 124,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073547,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 926,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 112,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073548,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 123,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 929,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073549,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 930,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 140,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073550,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 930,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 128,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073551,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 139,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 933,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073552,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 934,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 156,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073553,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 934,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 144,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073554,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 155,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 937,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073555,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 938,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 172,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073556,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 938,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 160,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073557,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 171,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 941,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073558,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 942,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 188,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073559,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 942,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 176,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073560,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 187,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 945,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073561,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 946,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 204,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073562,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 946,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 192,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073563,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 203,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 949,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073564,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 950,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 220,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073565,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 950,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 208,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073566,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 219,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 953,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073567,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 954,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 236,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073568,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 954,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 224,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073569,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 235,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 957,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073570,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 958,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 252,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073571,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 958,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 240,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073572,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 251,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 961,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073573,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 962,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 268,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073574,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 962,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 256,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073575,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 267,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 965,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073576,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 966,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 284,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073577,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 966,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 272,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073578,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 283,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 969,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073579,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 970,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 300,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073580,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 970,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 288,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073581,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 299,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 973,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073582,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 974,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 316,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073583,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 974,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 304,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073584,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 315,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 977,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073585,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 978,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 332,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073586,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 978,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 320,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073587,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 331,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 981,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073588,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 982,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 348,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073589,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 982,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 336,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073590,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 347,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 985,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073591,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 986,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 364,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073592,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 986,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 352,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073593,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 363,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 989,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073594,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 990,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 380,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073595,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 990,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 368,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073596,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 379,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 993,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073597,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 994,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 396,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073598,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 994,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 384,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073599,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 395,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 997,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073600,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 998,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 876,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073601,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 998,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 864,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073602,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 875,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1001,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073603,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1002,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 892,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073604,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1002,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 880,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073605,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 891,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1005,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073606,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1006,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 908,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073607,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1006,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 896,
                            slot: 0,
                            pattern: 10,
                        },
                    }];
    }
    #[inline(always)]
    fn lift_m31(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    #[inline(always)]
    fn selector_mask_sum_16(values: [QM31; 16], mask: u16) -> QM31 {
        match mask {
            1749 =>
                QM31::ZERO.add(values[0]).add(values[2]).add(values[4]).add(values[6]).add(values[7]).add(values[9]).add(values[10]),
            2048 => QM31::ZERO.add(values[11]),
            2049 => QM31::ZERO.add(values[0]).add(values[11]),
            4097 => QM31::ZERO.add(values[0]).add(values[12]),
            6144 => QM31::ZERO.add(values[11]).add(values[12]),
            6145 => QM31::ZERO.add(values[0]).add(values[11]).add(values[12]),
            26214 =>
                QM31::ZERO.add(values[1]).add(values[2]).add(values[5]).add(values[6]).add(values[9]).add(values[10]).add(values[13]).add(values[14]),
            _ => {
                ::core::panicking::panic_fmt(format_args!("outside frozen active mask set"));
            }
        }
    }
    pub(crate) struct Selectors {
        pub(crate) high: [QM31; 64],
        pub(crate) low: [QM31; 16],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Selectors { }
    #[automatically_derived]
    impl ::core::clone::Clone for Selectors {
        #[inline]
        fn clone(&self) -> Selectors {
            let _: ::core::clone::AssertParamIsClone<[QM31; 64]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 16]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Selectors { }
    impl Selectors {
        fn expand<const N :
            usize>(point: &[QM31; 10], start: usize, count: usize)
            -> [QM31; N] {
            let mut weights = [QM31::ZERO; N];
            weights[0] = QM31::ONE;
            let mut len = 1usize;
            let mut coordinate = start;
            while coordinate < start + count {
                let prepared = PreparedQm31Multiplier::new(point[coordinate]);
                let mut index = len;
                while index > 0 {
                    index -= 1;
                    let parent = weights[index];
                    let right = prepared.mul(parent);
                    weights[2 * index] = parent.sub(right);
                    weights[2 * index + 1] = right;
                }
                len *= 2;
                coordinate += 1;
            }
            weights
        }
        pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
            Self {
                high: Self::expand(point, 0, 6),
                low: Self::expand(point, 6, 4),
            }
        }
        #[inline(never)]
        pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Self {
            Self::at_point(point)
        }
        #[inline(always)]
        pub(crate) fn row(&self, row: usize) -> QM31 {
            if false {
                if !(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1) {
                    ::core::panicking::panic("assertion failed: row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1")
                };
            };
            self.high[row >> 4].mul(self.low[row & 15])
        }
        fn active_literal(&self) -> QM31 {
            let mut sum = QM31::ZERO;
            let mut block = 0usize;
            while block < 64 {
                sum = active_block227(*self, block, sum);
                block += 1;
            }
            sum
        }
        #[inline(always)]
        fn active(&self) -> QM31 { return self.active_literal(); }
    }
    fn pattern_values_literal(openings: &[QM31; POSEIDON2_WIDTH],
        lambda: QM31)
        -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
        let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
        let mut power = lambda;
        let mut limb = 0usize;
        while limb < POSEIDON2_WIDTH {
            powers[limb] = power;
            power = power.mul(lambda);
            limb += 1;
        }
        let mut result =
            [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
        let mut pattern_index = 0usize;
        while pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 {
            let pattern = constants::COPY_PATTERNS[pattern_index];
            let mut value = QM31::ZERO;
            limb = 0;
            while limb < POSEIDON2_WIDTH {
                value =
                    pattern_limb227(pattern, limb, *openings, powers, value);
                limb += 1;
            }
            result[pattern_index] = value;
            pattern_index += 1;
        }
        result
    }
    fn pattern_values(openings: &[QM31; POSEIDON2_WIDTH], lambda: QM31)
        -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
        return pattern_values_literal(openings, lambda);
    }
    struct CopyRowExtension {
        producer_values: [QM31; 2],
        producer_weights: [QM31; 2],
        consumer_values: [QM31; 2],
        consumer_weights: [QM31; 2],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CopyRowExtension { }
    #[automatically_derived]
    impl ::core::clone::Clone for CopyRowExtension {
        #[inline]
        fn clone(&self) -> CopyRowExtension {
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CopyRowExtension { }
    fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
        let denominators =
            [chi.sub(row.producer_values[0]), chi.sub(row.producer_values[1]),
                    chi.sub(row.consumer_values[0]),
                    chi.sub(row.consumer_values[1])];
        let producer_denominator = denominators[0].mul(denominators[1]);
        let consumer_denominator = denominators[2].mul(denominators[3]);
        let producer_numerator =
            row.producer_weights[0].mul(denominators[1]).add(row.producer_weights[1].mul(denominators[0]));
        let consumer_numerator =
            row.consumer_weights[0].mul(denominators[3]).add(row.consumer_weights[1].mul(denominators[2]));
        producer_denominator.mul(helper.mul(consumer_denominator).add(consumer_numerator)).sub(consumer_denominator.mul(producer_numerator))
    }
    #[inline(always)]
    fn link_weight(link: CompiledPoolV1PairForestLink, append_index: u64,
        variant: PoolV1PairForestCompiledVariantV1) -> M31 {
        match link.weight_kind {
            0 => M31::ONE,
            1 =>
                M31(u32::from(variant ==
                            PoolV1PairForestCompiledVariantV1::PrivateTransfer)),
            2 =>
                M31(u32::from(variant ==
                            PoolV1PairForestCompiledVariantV1::Withdrawal)),
            3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),
            4 => M31(((append_index >> link.weight_level) & 1) as u32),
            _ => {
                ::core::panicking::panic_fmt(format_args!("internal error: entered unreachable code: {0}",
                        format_args!("generated Pool V1 pair-forest Copy weight")));
            }
        }
    }
    fn accumulate_endpoint(values: &mut [QM31; 2], weights: &mut [QM31; 2],
        endpoint: CompiledPoolV1PairForestEndpoint, tag: u32, weight: M31,
        patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
        selectors: &Selectors) {
        let selector = selectors.row(usize::from(endpoint.row));
        let slot = usize::from(endpoint.slot);
        { weights[slot] = weights[slot].add(selector.mul_m31(weight)); }
        let compressed =
            lift_m31(M31(tag)).add(patterns[usize::from(endpoint.pattern)]);
        values[slot] = values[slot].add(selector.mul(compressed));
    }
    pub(crate) fn evaluate_with_selectors(openings: &[QM31; POSEIDON2_WIDTH],
        h1_z: QM31, selectors: &Selectors, lambda: QM31, chi: QM31,
        append_index: u64, variant: PoolV1PairForestCompiledVariantV1)
        -> PoolV1PairForestCompiledCopyTerminalV1 {
        let patterns = pattern_values(openings, lambda);
        let mut row =
            CopyRowExtension {
                producer_values: [QM31::ZERO; 2],
                producer_weights: [QM31::ZERO; 2],
                consumer_values: [QM31::ZERO; 2],
                consumer_weights: [QM31::ZERO; 2],
            };
        let mut link_index = 0usize;
        while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
            let link = constants::COPY_LINKS[link_index];
            let weight = link_weight(link, append_index, variant);
            {
                accumulate_endpoint(&mut row.producer_values,
                    &mut row.producer_weights, link.producer, link.tag, weight,
                    &patterns, selectors);
                accumulate_endpoint(&mut row.consumer_values,
                    &mut row.consumer_weights, link.consumer, link.tag, weight,
                    &patterns, selectors);
            }
            link_index += 1;
        }
        let active = selectors.active();
        PoolV1PairForestCompiledCopyTerminalV1 {
            residual: active.mul(copy_residual(row, h1_z, chi)),
            active,
        }
    }
    /// Evaluate the exact 136-link pair-forest Copy lane from the frozen sixteen
    /// merged-C1 openings and one H1 opening. This performs one fixed-size
    /// selector allocation and, under the selected tensor-basis evaluator, one
    /// fixed 103-QM31 scratch allocation. There is no registry- or input-dependent
    /// allocation.
    pub fn evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(openings:
            &[QM31; POSEIDON2_WIDTH], h1_z: QM31, point: &[QM31; 10],
        lambda: QM31, chi: QM31, append_index: u64,
        variant: PoolV1PairForestCompiledVariantV1)
        -> PoolV1PairForestCompiledCopyTerminalV1 {
        let selectors = Selectors::boxed_at_point(point);
        evaluate_with_selectors(openings, h1_z, &selectors, lambda, chi,
            append_index, variant)
    }
    pub fn pool_v1_pair_forest_copy_active_at_point_compiled_v1(point:
            &[QM31; 10]) -> QM31 {
        Selectors::at_point(point).active()
    }
    /// Source-extraction wrapper for a Boolean terminal row. `variant` is zero
    /// for private transfer and one for withdrawal.
    #[doc(hidden)]
    pub fn pool_v1_pair_forest_copy_lane_boolean_extraction_v1(variant: u8,
        selected_row: u16, openings: &[QM31; POSEIDON2_WIDTH], h1_z: QM31,
        lambda: QM31, chi: QM31, append_index: u64)
        -> Option<PoolV1PairForestCompiledCopyTerminalV1> {
        if usize::from(selected_row) >=
                POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1 {
            return None;
        }
        let variant =
            match variant {
                0 => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
                1 => PoolV1PairForestCompiledVariantV1::Withdrawal,
                _ => return None,
            };
        let mut high = [QM31::ZERO; 64];
        let mut low = [QM31::ZERO; 16];
        high[usize::from(selected_row >> 4)] = QM31::ONE;
        low[usize::from(selected_row & 15)] = QM31::ONE;
        let selectors = Selectors { high, low };
        Some(evaluate_with_selectors(openings, h1_z, &selectors, lambda, chi,
                append_index, variant))
    }
    #[inline(always)]
    fn pattern_window(openings: &[QM31; POSEIDON2_WIDTH],
        prepared: [PreparedQm31Multiplier; 8], start: usize) -> QM31 {
        let mut value = QM31::ZERO;
        let mut slot = 0usize;
        while slot < 8 {
            value = value.add(prepared[slot].mul(openings[start + slot]));
            slot += 1;
        }
        value
    }
    fn pattern_limb227(pattern: CompiledPoolV1PairForestPattern, limb: usize,
        openings: [QM31; 16], powers: [QM31; 16], value: QM31) -> QM31 {
        if pattern.kinds[limb] == 1 {
            let source =
                openings[usize::from(pattern.columns[limb])].add(lift_m31(M31(pattern.offsets[limb])));
            value.add(powers[limb].mul(source))
        } else { value }
    }
    fn active_block227(selectors: Selectors, block: usize, sum: QM31)
        -> QM31 {
        let mask = constants::ACTIVE_ROW_MASKS[block];
        if mask != 0 {
            sum.add(selectors.high[block].mul(selector_mask_sum_16(selectors.low,
                        mask)))
        } else { sum }
    }
    fn mask_step227(values: [QM31; 16], index: usize, sum: QM31,
        complement: bool) -> QM31 {
        if complement {
            sum.sub(values[index])
        } else { sum.add(values[index]) }
    }
}
mod reference_field {
    //! Gated terminal arithmetic helpers; same field operation and accumulation order.
    use aspis_core::field::{M31, CM31, QM31, P};
    #[inline(always)]
    fn cm31_mul_r(value: CM31) -> CM31 {
        CM31::new(value.a.double().sub(value.b),
            value.a.add(value.b.double()))
    }
    pub(crate) struct PreparedQm31Multiplier {
        components: [[M31; 3]; 3],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for PreparedQm31Multiplier { }
    #[automatically_derived]
    impl ::core::clone::Clone for PreparedQm31Multiplier {
        #[inline]
        fn clone(&self) -> PreparedQm31Multiplier {
            let _: ::core::clone::AssertParamIsClone<[[M31; 3]; 3]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PreparedQm31Multiplier { }
    #[inline(always)]
    fn prepare_component(component: CM31) -> [M31; 3] {
        [component.a, component.b, component.a.add(component.b)]
    }
    #[inline(always)]
    fn prepared_component_mul(left: [M31; 3], right: CM31) -> CM31 {
        let m0 = left[0].mul(right.a);
        let m1 = left[1].mul(right.b);
        let m2 = left[2].mul(right.a.add(right.b));
        CM31 { a: m0.sub(m1), b: m2.sub(m0).sub(m1) }
    }
    impl PreparedQm31Multiplier {
        #[inline(always)]
        pub(crate) fn new(value: QM31) -> Self {
            Self {
                components: [prepare_component(value.c0),
                        prepare_component(value.c1),
                        prepare_component(value.c0.add(value.c1))],
            }
        }
        #[inline(always)]
        pub(crate) fn mul(self, rhs: QM31) -> QM31 {
            let m0 = prepared_component_mul(self.components[0], rhs.c0);
            let m1 = prepared_component_mul(self.components[1], rhs.c1);
            let m2 =
                prepared_component_mul(self.components[2],
                    rhs.c0.add(rhs.c1));
            QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
        }
    }
    #[inline(always)]
    fn reconstruct_component(channels: [u64; 3]) -> CM31 {
        let m0 = M31::reduce_u64(channels[0]);
        let m1 = M31::reduce_u64(channels[1]);
        let m2 = M31::reduce_u64(channels[2]);
        CM31 { a: m0.sub(m1), b: m2.sub(m0).sub(m1) }
    }
    #[inline(always)]
    fn reconstruct_channels(sums: [[u64; 3]; 3]) -> QM31 {
        let m0 = reconstruct_component(sums[0]);
        let m1 = reconstruct_component(sums[1]);
        let m2 = reconstruct_component(sums[2]);
        QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
    }
    #[inline(always)]
    fn accumulate_channels(mut sums: [[u64; 3]; 3], left: QM31, right: QM31)
        -> [[u64; 3]; 3] {
        let left_sum = left.c0.add(left.c1);
        let right_sum = right.c0.add(right.c1);
        let a =
            [[left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
                    [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
                    [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)]];
        let b =
            [[right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
                    [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
                    [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)]];
        sums[0][0] += a[0][0].0 as u64 * b[0][0].0 as u64;
        sums[0][1] += a[0][1].0 as u64 * b[0][1].0 as u64;
        sums[0][2] += a[0][2].0 as u64 * b[0][2].0 as u64;
        sums[1][0] += a[1][0].0 as u64 * b[1][0].0 as u64;
        sums[1][1] += a[1][1].0 as u64 * b[1][1].0 as u64;
        sums[1][2] += a[1][2].0 as u64 * b[1][2].0 as u64;
        sums[2][0] += a[2][0].0 as u64 * b[2][0].0 as u64;
        sums[2][1] += a[2][1].0 as u64 * b[2][1].0 as u64;
        sums[2][2] += a[2][2].0 as u64 * b[2][2].0 as u64;
        sums
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products2(left: [QM31; 2], right: [QM31; 2])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products3(left: [QM31; 3], right: [QM31; 3])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        let sums = accumulate_channels(sums, left[2], right[2]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products4(left: [QM31; 4], right: [QM31; 4])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        let sums = accumulate_channels(sums, left[2], right[2]);
        let sums = accumulate_channels(sums, left[3], right[3]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    fn terminal_limb(value: M31) -> u64 { u64::from(value.0) }
    #[inline(always)]
    pub(crate) fn qm31_pack_base4(values: &[QM31]) -> QM31 {
        if !(values.len() <= 4) {
            ::core::panicking::panic("assertion failed: values.len() <= 4")
        };
        let mut padded = [QM31::ZERO; 4];
        let mut i = 0usize;
        while i < values.len() { padded[i] = values[i]; i += 1; }
        let [v0, v1, v2, v3] = padded;
        let p = u64::from(P);
        let c0_a =
            terminal_limb(v0.c0.a) + (p - terminal_limb(v1.c0.b)) +
                            2 * terminal_limb(v2.c1.a) + (p - terminal_limb(v2.c1.b)) +
                    (p - terminal_limb(v3.c1.a)) +
                (2 * p - 2 * terminal_limb(v3.c1.b));
        let c0_b =
            terminal_limb(v0.c0.b) + terminal_limb(v1.c0.a) +
                            terminal_limb(v2.c1.a) + 2 * terminal_limb(v2.c1.b) +
                    2 * terminal_limb(v3.c1.a) + (p - terminal_limb(v3.c1.b));
        let c1_a =
            terminal_limb(v0.c1.a) + (p - terminal_limb(v1.c1.b)) +
                    terminal_limb(v2.c0.a) + (p - terminal_limb(v3.c0.b));
        let c1_b =
            terminal_limb(v0.c1.b) + terminal_limb(v1.c1.a) +
                    terminal_limb(v2.c0.b) + terminal_limb(v3.c0.a);
        QM31 {
            c0: CM31::new(M31::reduce_u64(c0_a), M31::reduce_u64(c0_b)),
            c1: CM31::new(M31::reduce_u64(c1_a), M31::reduce_u64(c1_b)),
        }
    }
    fn accumulate_prepared227(mut sums: [[u64; 3]; 3], right: QM31,
        left: PreparedQm31Multiplier) -> [[u64; 3]; 3] {
        let right_sum = right.c0.add(right.c1);
        let right_components =
            [[right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
                    [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
                    [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)]];
        sums[0][0] +=
            left.components[0][0].0 as u64 * right_components[0][0].0 as u64;
        sums[0][1] +=
            left.components[0][1].0 as u64 * right_components[0][1].0 as u64;
        sums[0][2] +=
            left.components[0][2].0 as u64 * right_components[0][2].0 as u64;
        sums[1][0] +=
            left.components[1][0].0 as u64 * right_components[1][0].0 as u64;
        sums[1][1] +=
            left.components[1][1].0 as u64 * right_components[1][1].0 as u64;
        sums[1][2] +=
            left.components[1][2].0 as u64 * right_components[1][2].0 as u64;
        sums[2][0] +=
            left.components[2][0].0 as u64 * right_components[2][0].0 as u64;
        sums[2][1] +=
            left.components[2][1].0 as u64 * right_components[2][1].0 as u64;
        sums[2][2] +=
            left.components[2][2].0 as u64 * right_components[2][2].0 as u64;
        sums
    }
    pub(crate) fn qm31_sum_products3_prepared(left:
            &[PreparedQm31Multiplier; 3], right: &[QM31; 3]) -> QM31 {
        let mut sums = [[0u64; 3]; 3];
        sums = accumulate_prepared227(sums, right[0], left[0]);
        sums = accumulate_prepared227(sums, right[1], left[1]);
        sums = accumulate_prepared227(sums, right[2], left[2]);
        let m0 = reconstruct_component(sums[0]);
        let m1 = reconstruct_component(sums[1]);
        let m2 = reconstruct_component(sums[2]);
        QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
    }
    pub(crate) fn qm31_m31_dot(weights: &[QM31; 7], values: &[M31; 7])
        -> QM31 {
        let mut sums = [0u64; 4];
        {
            let mut raw = [0u64; 4];
            {
                let value = values[0].0 as u64;
                let weight = weights[0];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            {
                let value = values[1].0 as u64;
                let weight = weights[1];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            {
                let value = values[2].0 as u64;
                let weight = weights[2];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            {
                let value = values[3].0 as u64;
                let weight = weights[3];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            sums[0] += M31::reduce_u64(raw[0]).0 as u64;
            sums[1] += M31::reduce_u64(raw[1]).0 as u64;
            sums[2] += M31::reduce_u64(raw[2]).0 as u64;
            sums[3] += M31::reduce_u64(raw[3]).0 as u64;
        }
        {
            let mut raw = [0u64; 4];
            {
                let value = values[4].0 as u64;
                let weight = weights[4];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            {
                let value = values[5].0 as u64;
                let weight = weights[5];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            {
                let value = values[6].0 as u64;
                let weight = weights[6];
                raw[0] += weight.c0.a.0 as u64 * value;
                raw[1] += weight.c0.b.0 as u64 * value;
                raw[2] += weight.c1.a.0 as u64 * value;
                raw[3] += weight.c1.b.0 as u64 * value;
            }
            sums[0] += M31::reduce_u64(raw[0]).0 as u64;
            sums[1] += M31::reduce_u64(raw[1]).0 as u64;
            sums[2] += M31::reduce_u64(raw[2]).0 as u64;
            sums[3] += M31::reduce_u64(raw[3]).0 as u64;
        }
        QM31 {
            c0: CM31::new(M31::reduce_u64(sums[0]), M31::reduce_u64(sums[1])),
            c1: CM31::new(M31::reduce_u64(sums[2]), M31::reduce_u64(sums[3])),
        }
    }
}
mod reference_poseidon {
    use crate::reference_field::{
        qm31_m31_dot, qm31_pack_base4, qm31_sum_products3_prepared,
        PreparedQm31Multiplier,
    };
    use aspis_core::field::{qm31_sum_products4, CM31, M31, P, QM31};
    use aspis_statement::poseidon2::{POSEIDON2_WIDTH, RATE};
    use aspis_statement::state_only_poseidon::{
        StateOnlyPoseidonOpenings, StateOnlyPoseidonSelectors,
        STATE_ONLY_POSEIDON_PACKED_LANES,
    };
    macro_rules! array4 {
        ($index:ident,$body:expr) =>
        {{
                let mut
                output=[{let
                    $index=0usize;$body},{let
                    $index=1usize;$body},{let
                    $index=2usize;$body},{let $index=3usize;$body}]; output
            }};
    }
    pub(crate) const EXTERNAL_INITIAL: [[u32; 16]; 4] =
        [[0x768bab52, 0x70e0ab7d, 0x3d266c8a, 0x6da42045, 0x600fef22,
                        0x41dace6b, 0x64f9bdd4, 0x5d42d4fe, 0x76b1516d, 0x6fc9a717,
                        0x70ac4fb6, 0x00194ef6, 0x22b644e2, 0x1f7916d5, 0x47581be2,
                        0x2710a123],
                [0x6284e867, 0x018d3afe, 0x5df99ef3, 0x4c1e467b, 0x566f6abc,
                        0x2994e427, 0x538a6d42, 0x5d7bf2cf, 0x7fda2dab, 0x0fd854c4,
                        0x46922fca, 0x3d7763a1, 0x19fd05ca, 0x0a4bbb43, 0x15075851,
                        0x3d903d76],
                [0x2d290ff7, 0x40809fa0, 0x59dac6ec, 0x127927a2, 0x6bbf0ea0,
                        0x0294140f, 0x24742976, 0x6e84c081, 0x22484f4a, 0x354cae59,
                        0x0453ffe1, 0x3f47a3cc, 0x0088204e, 0x6066e109, 0x3b7c4b80,
                        0x6b55665d],
                [0x3bc4b897, 0x735bf378, 0x508daf42, 0x1884fc2b, 0x7214f24c,
                        0x7498be0a, 0x1a60e640, 0x3303f928, 0x29b46376, 0x5c96bb68,
                        0x65d097a5, 0x1d358e9f, 0x4a9a9017, 0x4724cf76, 0x347af70f,
                        0x1e77e59a]];
    pub(crate) const EXTERNAL_FINAL: [[u32; 16]; 4] =
        [[0x57090613, 0x1fa42108, 0x17bbef50, 0x1ff7e11c, 0x047b24ca,
                        0x4e140275, 0x4fa086f5, 0x079b309c, 0x1159bd47, 0x6d37e4e5,
                        0x075d8dce, 0x12121ca0, 0x7f6a7c40, 0x68e182ba, 0x5493201b,
                        0x0444a80e],
                [0x0064f4c6, 0x6467abe6, 0x66975762, 0x2af68f9b, 0x345b33be,
                        0x1b70d47f, 0x053db717, 0x381189cb, 0x43b915f8, 0x20df3694,
                        0x0f459d26, 0x77a0e97b, 0x2f73e739, 0x1876c2f9, 0x65a0e29a,
                        0x4cabefbe],
                [0x5abd1268, 0x4d34a760, 0x12771799, 0x69a0c9ac, 0x39091e55,
                        0x7f611cd0, 0x3af055da, 0x7ac0bbdf, 0x6e0f3a24, 0x41e3b6f7,
                        0x49b3756d, 0x568bc538, 0x20c079d8, 0x1701c72c, 0x7670dc6c,
                        0x5a439035],
                [0x7c93e00e, 0x561fbb4d, 0x1178907b, 0x02737406, 0x32fb24f1,
                        0x6323b60a, 0x6ab12418, 0x42c99cea, 0x155a0b97, 0x53d1c6aa,
                        0x2bd20347, 0x279b3d73, 0x4f5f3c70, 0x0245af6c, 0x238359d3,
                        0x49966a59]];
    pub(crate) const INTERNAL: [u32; 14] =
        [0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd,
                0x66685c7f, 0x78d3249a, 0x60187881, 0x76dad67a, 0x0690b437,
                0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21];
    fn lift(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    #[inline(always)]
    fn pow5(value: QM31) -> QM31 {
        let square = value.square();
        square.square().mul(value)
    }
    #[inline(always)]
    fn extension_limbs(value: QM31) -> [u32; 4] {
        [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
    }
    #[inline(always)]
    fn extension_from_raw_limbs(limbs: [u64; 4]) -> QM31 {
        QM31 {
            c0: CM31::new(M31::reduce_u62(limbs[0]),
                M31::reduce_u62(limbs[1])),
            c1: CM31::new(M31::reduce_u62(limbs[2]),
                M31::reduce_u62(limbs[3])),
        }
    }
    /// Addition-only Poseidon external layer with one reduction per output limb.
    #[inline(never)]
    fn external_linear_lazy(state: &mut [QM31; 16]) {
        {
            let input = [state[0], state[1], state[2], state[3]];
            let output = external_group227(input);
            state[0] = output[0];
            state[1] = output[1];
            state[2] = output[2];
            state[3] = output[3];
        }
        {
            let input = [state[4], state[5], state[6], state[7]];
            let output = external_group227(input);
            state[4] = output[0];
            state[5] = output[1];
            state[6] = output[2];
            state[7] = output[3];
        }
        {
            let input = [state[8], state[9], state[10], state[11]];
            let output = external_group227(input);
            state[8] = output[0];
            state[9] = output[1];
            state[10] = output[2];
            state[11] = output[3];
        }
        {
            let input = [state[12], state[13], state[14], state[15]];
            let output = external_group227(input);
            state[12] = output[0];
            state[13] = output[1];
            state[14] = output[2];
            state[15] = output[3];
        }
        let sums = global_sums227(*state);
        state[0] = add_global227(state[0], sums[0]);
        state[1] = add_global227(state[1], sums[1]);
        state[2] = add_global227(state[2], sums[2]);
        state[3] = add_global227(state[3], sums[3]);
        state[4] = add_global227(state[4], sums[0]);
        state[5] = add_global227(state[5], sums[1]);
        state[6] = add_global227(state[6], sums[2]);
        state[7] = add_global227(state[7], sums[3]);
        state[8] = add_global227(state[8], sums[0]);
        state[9] = add_global227(state[9], sums[1]);
        state[10] = add_global227(state[10], sums[2]);
        state[11] = add_global227(state[11], sums[3]);
        state[12] = add_global227(state[12], sums[0]);
        state[13] = add_global227(state[13], sums[1]);
        state[14] = add_global227(state[14], sums[2]);
        state[15] = add_global227(state[15], sums[3]);
    }
    const EXTERNAL_LOCAL_LIMB_MODULUS_BOUND: u64 = 7 * P as u64;
    const _: () =
        if !(8 * EXTERNAL_LOCAL_LIMB_MODULUS_BOUND < (1u64 << 62)) {
            ::core::panicking::panic("assertion failed: 8 * EXTERNAL_LOCAL_LIMB_MODULUS_BOUND < (1u64 << 62)")
        };
    /// Apply the local external matrix and the tower-basis packing functional in
    /// one raw-limb pass.
    ///
    /// If `t[r,l] = sum_j B[r,j] * input[j,l]`, packing the four local outputs
    /// against `(1, i, u, i*u)` gives exactly
    ///
    /// ```text
    /// c0.a = t[0,a] - t[1,b] + 2t[2,c] - t[2,d] - t[3,c] - 2t[3,d]
    /// c0.b = t[0,b] + t[1,a] + t[2,c] + 2t[2,d] + 2t[3,c] - t[3,d]
    /// c1.a = t[0,c] - t[1,d] + t[2,a] - t[3,b]
    /// c1.b = t[0,d] + t[1,c] + t[2,b] + t[3,a]
    /// ```
    ///
    /// The signed offsets below are multiples of P and do not change the field
    /// value. The first two raw outputs are below `56P`; the last two are below
    /// `28P`. Thus one final reduction per output limb is sufficient.
    #[inline(always)]
    fn external_local_packed_raw(input: [QM31; 4]) -> [u64; 4] {
        let input =
            [extension_limbs(input[0]), extension_limbs(input[1]),
                    extension_limbs(input[2]), extension_limbs(input[3])];
        let local: [[u64; 4]; 4] =
            {
                let mut output =
                    [{
                                let output = 0usize;
                                {
                                    {
                                        let mut output =
                                            [{
                                                        let limb = 0usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 1usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 2usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 3usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    }];
                                        output
                                    }
                                }
                            },
                            {
                                let output = 1usize;
                                {
                                    {
                                        let mut output =
                                            [{
                                                        let limb = 0usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 1usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 2usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 3usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    }];
                                        output
                                    }
                                }
                            },
                            {
                                let output = 2usize;
                                {
                                    {
                                        let mut output =
                                            [{
                                                        let limb = 0usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 1usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 2usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 3usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    }];
                                        output
                                    }
                                }
                            },
                            {
                                let output = 3usize;
                                {
                                    {
                                        let mut output =
                                            [{
                                                        let limb = 0usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 1usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 2usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    },
                                                    {
                                                        let limb = 3usize;
                                                        {
                                                            let a = u64::from(input[0][limb]);
                                                            let b = u64::from(input[1][limb]);
                                                            let c = u64::from(input[2][limb]);
                                                            let d = u64::from(input[3][limb]);
                                                            raw_limb227(output, a, b, c, d)
                                                        }
                                                    }];
                                        output
                                    }
                                }
                            }];
                output
            };
        let mut all_local_limbs_bounded = true;
        let mut output = 0usize;
        let mut limb = 0usize;
        all_local_limbs_bounded &=
            local[0usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[0usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[0usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[0usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        let mut limb = 0usize;
        all_local_limbs_bounded &=
            local[1usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[1usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[1usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[1usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        let mut limb = 0usize;
        all_local_limbs_bounded &=
            local[2usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[2usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[2usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[2usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        let mut limb = 0usize;
        all_local_limbs_bounded &=
            local[3usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[3usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[3usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        all_local_limbs_bounded &=
            local[3usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        if false {
            if !all_local_limbs_bounded {
                ::core::panicking::panic("assertion failed: all_local_limbs_bounded")
            };
        };
        let bound = EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
        let packed =
            [local[0][0] + 5 * bound - local[1][1] + 2 * local[2][2] -
                                local[2][3] - local[3][2] - 2 * local[3][3],
                    local[0][1] + local[1][0] + local[2][2] + 2 * local[2][3] +
                                2 * local[3][2] + bound - local[3][3],
                    local[0][2] + 2 * bound - local[1][3] + local[2][0] -
                        local[3][1],
                    local[0][3] + local[1][2] + local[2][1] + local[3][0]];
        if false {
            if !(packed[0] < 8 * bound) {
                ::core::panicking::panic("assertion failed: packed[0] < 8 * bound")
            };
        };
        if false {
            if !(packed[1] < 8 * bound) {
                ::core::panicking::panic("assertion failed: packed[1] < 8 * bound")
            };
        };
        if false {
            if !(packed[2] < 4 * bound) {
                ::core::panicking::panic("assertion failed: packed[2] < 4 * bound")
            };
        };
        if false {
            if !(packed[3] < 4 * bound) {
                ::core::panicking::panic("assertion failed: packed[3] < 4 * bound")
            };
        };
        packed
    }
    #[inline(always)]
    fn external_local_packed(input: [QM31; 4]) -> QM31 {
        extension_from_raw_limbs(external_local_packed_raw(input))
    }
    /// Apply the final external layer only through the four tower-packed output
    /// functionals consumed by the terminal composition.
    ///
    /// If `B` is the four-lane local matrix and `J + I` is the global layer, then
    /// packing commutes with both maps:
    ///
    /// `pack((J + I) B x)_g = pack(B x_g) + sum_h pack(B x_h)`.
    ///
    /// This is the transpose/adjoint form specialized to the fixed tower-basis
    /// functional.  It avoids materializing and reducing all sixteen final lanes
    /// and introduces no challenge-dependent dot products.
    #[inline(never)]
    fn external_linear_packed(state: [QM31; POSEIDON2_WIDTH]) -> [QM31; 4] {
        let mut local_packed = [QM31::ZERO; 4];
        let mut group = 0usize;
        let start = 4 * 0usize;
        let input =
            [state[start], state[start + 1], state[start + 2],
                    state[start + 3]];
        local_packed[0usize] = external_local_packed(input);
        let start = 4 * 1usize;
        let input =
            [state[start], state[start + 1], state[start + 2],
                    state[start + 3]];
        local_packed[1usize] = external_local_packed(input);
        let start = 4 * 2usize;
        let input =
            [state[start], state[start + 1], state[start + 2],
                    state[start + 3]];
        local_packed[2usize] = external_local_packed(input);
        let start = 4 * 3usize;
        let input =
            [state[start], state[start + 1], state[start + 2],
                    state[start + 3]];
        local_packed[3usize] = external_local_packed(input);
        let sum =
            QM31::ZERO.add(local_packed[0]).add(local_packed[1]).add(local_packed[2]).add(local_packed[3]);
        [local_packed[0].add(sum), local_packed[1].add(sum),
                local_packed[2].add(sum), local_packed[3].add(sum)]
    }
    #[inline(never)]
    fn internal_linear_lazy(state: &mut [QM31; 16]) {
        const SHIFTS: [u8; 15] =
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
        let old_zero = extension_limbs(state[0]);
        let mut part_sum = [0u64; 4];
        part_sum = internal_sum227(part_sum, state[1]);
        part_sum = internal_sum227(part_sum, state[2]);
        part_sum = internal_sum227(part_sum, state[3]);
        part_sum = internal_sum227(part_sum, state[4]);
        part_sum = internal_sum227(part_sum, state[5]);
        part_sum = internal_sum227(part_sum, state[6]);
        part_sum = internal_sum227(part_sum, state[7]);
        part_sum = internal_sum227(part_sum, state[8]);
        part_sum = internal_sum227(part_sum, state[9]);
        part_sum = internal_sum227(part_sum, state[10]);
        part_sum = internal_sum227(part_sum, state[11]);
        part_sum = internal_sum227(part_sum, state[12]);
        part_sum = internal_sum227(part_sum, state[13]);
        part_sum = internal_sum227(part_sum, state[14]);
        part_sum = internal_sum227(part_sum, state[15]);
        let full_sum = internal_full_sum227(part_sum, old_zero);
        state[0] = internal_zero227(part_sum, old_zero);
        state[1] = internal_shift227(state[1], full_sum, SHIFTS[0]);
        state[2] = internal_shift227(state[2], full_sum, SHIFTS[1]);
        state[3] = internal_shift227(state[3], full_sum, SHIFTS[2]);
        state[4] = internal_shift227(state[4], full_sum, SHIFTS[3]);
        state[5] = internal_shift227(state[5], full_sum, SHIFTS[4]);
        state[6] = internal_shift227(state[6], full_sum, SHIFTS[5]);
        state[7] = internal_shift227(state[7], full_sum, SHIFTS[6]);
        state[8] = internal_shift227(state[8], full_sum, SHIFTS[7]);
        state[9] = internal_shift227(state[9], full_sum, SHIFTS[8]);
        state[10] = internal_shift227(state[10], full_sum, SHIFTS[9]);
        state[11] = internal_shift227(state[11], full_sum, SHIFTS[10]);
        state[12] = internal_shift227(state[12], full_sum, SHIFTS[11]);
        state[13] = internal_shift227(state[13], full_sum, SHIFTS[12]);
        state[14] = internal_shift227(state[14], full_sum, SHIFTS[13]);
        state[15] = internal_shift227(state[15], full_sum, SHIFTS[14]);
    }
    #[inline(never)]
    fn full_round(mut state: [QM31; POSEIDON2_WIDTH],
        constants: [QM31; POSEIDON2_WIDTH]) -> [QM31; POSEIDON2_WIDTH] {
        state[0usize] = pow5(state[0usize].add(constants[0usize]));
        state[1usize] = pow5(state[1usize].add(constants[1usize]));
        state[2usize] = pow5(state[2usize].add(constants[2usize]));
        state[3usize] = pow5(state[3usize].add(constants[3usize]));
        state[4usize] = pow5(state[4usize].add(constants[4usize]));
        state[5usize] = pow5(state[5usize].add(constants[5usize]));
        state[6usize] = pow5(state[6usize].add(constants[6usize]));
        state[7usize] = pow5(state[7usize].add(constants[7usize]));
        state[8usize] = pow5(state[8usize].add(constants[8usize]));
        state[9usize] = pow5(state[9usize].add(constants[9usize]));
        state[10usize] = pow5(state[10usize].add(constants[10usize]));
        state[11usize] = pow5(state[11usize].add(constants[11usize]));
        state[12usize] = pow5(state[12usize].add(constants[12usize]));
        state[13usize] = pow5(state[13usize].add(constants[13usize]));
        state[14usize] = pow5(state[14usize].add(constants[14usize]));
        state[15usize] = pow5(state[15usize].add(constants[15usize]));
        external_linear_lazy(&mut state);
        state
    }
    /// Full round whose constants are pinned base-field values. Only c0.a changes
    /// during the addition, avoiding three zero-limb additions per lane in the
    /// two fixed leading rounds.
    #[inline(never)]
    fn full_round_m31_constants(mut state: [QM31; POSEIDON2_WIDTH],
        constants: [u32; POSEIDON2_WIDTH]) -> [QM31; POSEIDON2_WIDTH] {
        state[0usize].c0.a = state[0usize].c0.a.add(M31(constants[0usize]));
        state[0usize] = pow5(state[0usize]);
        state[1usize].c0.a = state[1usize].c0.a.add(M31(constants[1usize]));
        state[1usize] = pow5(state[1usize]);
        state[2usize].c0.a = state[2usize].c0.a.add(M31(constants[2usize]));
        state[2usize] = pow5(state[2usize]);
        state[3usize].c0.a = state[3usize].c0.a.add(M31(constants[3usize]));
        state[3usize] = pow5(state[3usize]);
        state[4usize].c0.a = state[4usize].c0.a.add(M31(constants[4usize]));
        state[4usize] = pow5(state[4usize]);
        state[5usize].c0.a = state[5usize].c0.a.add(M31(constants[5usize]));
        state[5usize] = pow5(state[5usize]);
        state[6usize].c0.a = state[6usize].c0.a.add(M31(constants[6usize]));
        state[6usize] = pow5(state[6usize]);
        state[7usize].c0.a = state[7usize].c0.a.add(M31(constants[7usize]));
        state[7usize] = pow5(state[7usize]);
        state[8usize].c0.a = state[8usize].c0.a.add(M31(constants[8usize]));
        state[8usize] = pow5(state[8usize]);
        state[9usize].c0.a = state[9usize].c0.a.add(M31(constants[9usize]));
        state[9usize] = pow5(state[9usize]);
        state[10usize].c0.a =
            state[10usize].c0.a.add(M31(constants[10usize]));
        state[10usize] = pow5(state[10usize]);
        state[11usize].c0.a =
            state[11usize].c0.a.add(M31(constants[11usize]));
        state[11usize] = pow5(state[11usize]);
        state[12usize].c0.a =
            state[12usize].c0.a.add(M31(constants[12usize]));
        state[12usize] = pow5(state[12usize]);
        state[13usize].c0.a =
            state[13usize].c0.a.add(M31(constants[13usize]));
        state[13usize] = pow5(state[13usize]);
        state[14usize].c0.a =
            state[14usize].c0.a.add(M31(constants[14usize]));
        state[14usize] = pow5(state[14usize]);
        state[15usize].c0.a =
            state[15usize].c0.a.add(M31(constants[15usize]));
        state[15usize] = pow5(state[15usize]);
        external_linear_lazy(&mut state);
        state
    }
    #[inline(never)]
    fn full_round_packed(mut state: [QM31; POSEIDON2_WIDTH],
        constants: [QM31; POSEIDON2_WIDTH])
        -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        state[0usize] = pow5(state[0usize].add(constants[0usize]));
        state[1usize] = pow5(state[1usize].add(constants[1usize]));
        state[2usize] = pow5(state[2usize].add(constants[2usize]));
        state[3usize] = pow5(state[3usize].add(constants[3usize]));
        state[4usize] = pow5(state[4usize].add(constants[4usize]));
        state[5usize] = pow5(state[5usize].add(constants[5usize]));
        state[6usize] = pow5(state[6usize].add(constants[6usize]));
        state[7usize] = pow5(state[7usize].add(constants[7usize]));
        state[8usize] = pow5(state[8usize].add(constants[8usize]));
        state[9usize] = pow5(state[9usize].add(constants[9usize]));
        state[10usize] = pow5(state[10usize].add(constants[10usize]));
        state[11usize] = pow5(state[11usize].add(constants[11usize]));
        state[12usize] = pow5(state[12usize].add(constants[12usize]));
        state[13usize] = pow5(state[13usize].add(constants[13usize]));
        state[14usize] = pow5(state[14usize].add(constants[14usize]));
        state[15usize] = pow5(state[15usize].add(constants[15usize]));
        external_linear_packed(state)
    }
    #[inline(never)]
    fn full_round_m31_constants_packed(mut state: [QM31; POSEIDON2_WIDTH],
        constants: [u32; POSEIDON2_WIDTH])
        -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        state[0usize].c0.a = state[0usize].c0.a.add(M31(constants[0usize]));
        state[0usize] = pow5(state[0usize]);
        state[1usize].c0.a = state[1usize].c0.a.add(M31(constants[1usize]));
        state[1usize] = pow5(state[1usize]);
        state[2usize].c0.a = state[2usize].c0.a.add(M31(constants[2usize]));
        state[2usize] = pow5(state[2usize]);
        state[3usize].c0.a = state[3usize].c0.a.add(M31(constants[3usize]));
        state[3usize] = pow5(state[3usize]);
        state[4usize].c0.a = state[4usize].c0.a.add(M31(constants[4usize]));
        state[4usize] = pow5(state[4usize]);
        state[5usize].c0.a = state[5usize].c0.a.add(M31(constants[5usize]));
        state[5usize] = pow5(state[5usize]);
        state[6usize].c0.a = state[6usize].c0.a.add(M31(constants[6usize]));
        state[6usize] = pow5(state[6usize]);
        state[7usize].c0.a = state[7usize].c0.a.add(M31(constants[7usize]));
        state[7usize] = pow5(state[7usize]);
        state[8usize].c0.a = state[8usize].c0.a.add(M31(constants[8usize]));
        state[8usize] = pow5(state[8usize]);
        state[9usize].c0.a = state[9usize].c0.a.add(M31(constants[9usize]));
        state[9usize] = pow5(state[9usize]);
        state[10usize].c0.a =
            state[10usize].c0.a.add(M31(constants[10usize]));
        state[10usize] = pow5(state[10usize]);
        state[11usize].c0.a =
            state[11usize].c0.a.add(M31(constants[11usize]));
        state[11usize] = pow5(state[11usize]);
        state[12usize].c0.a =
            state[12usize].c0.a.add(M31(constants[12usize]));
        state[12usize] = pow5(state[12usize]);
        state[13usize].c0.a =
            state[13usize].c0.a.add(M31(constants[13usize]));
        state[13usize] = pow5(state[13usize]);
        state[14usize].c0.a =
            state[14usize].c0.a.add(M31(constants[14usize]));
        state[14usize] = pow5(state[14usize]);
        state[15usize].c0.a =
            state[15usize].c0.a.add(M31(constants[15usize]));
        state[15usize] = pow5(state[15usize]);
        external_linear_packed(state)
    }
    #[inline(never)]
    fn internal_round(mut state: [QM31; POSEIDON2_WIDTH], constant: QM31)
        -> [QM31; 16] {
        state[0] = pow5(state[0].add(constant));
        internal_linear_lazy(&mut state);
        state
    }
    fn leading_pair(openings: &StateOnlyPoseidonOpenings)
        -> [QM31; POSEIDON2_WIDTH] {
        let mut state = openings.z;
        state[0usize] = state[0usize].add(openings.xor12_z[0usize]);
        state[1usize] = state[1usize].add(openings.xor12_z[1usize]);
        state[2usize] = state[2usize].add(openings.xor12_z[2usize]);
        state[3usize] = state[3usize].add(openings.xor12_z[3usize]);
        state[4usize] = state[4usize].add(openings.xor12_z[4usize]);
        state[5usize] = state[5usize].add(openings.xor12_z[5usize]);
        state[6usize] = state[6usize].add(openings.xor12_z[6usize]);
        state[7usize] = state[7usize].add(openings.xor12_z[7usize]);
        external_linear_lazy(&mut state);
        full_round_m31_constants(full_round_m31_constants(state,
                EXTERNAL_INITIAL[0]), EXTERNAL_INITIAL[1])
    }
    fn leading_pair_packed(openings: &StateOnlyPoseidonOpenings)
        -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        let mut state = openings.z;
        state[0usize] = state[0usize].add(openings.xor12_z[0usize]);
        state[1usize] = state[1usize].add(openings.xor12_z[1usize]);
        state[2usize] = state[2usize].add(openings.xor12_z[2usize]);
        state[3usize] = state[3usize].add(openings.xor12_z[3usize]);
        state[4usize] = state[4usize].add(openings.xor12_z[4usize]);
        state[5usize] = state[5usize].add(openings.xor12_z[5usize]);
        state[6usize] = state[6usize].add(openings.xor12_z[6usize]);
        state[7usize] = state[7usize].add(openings.xor12_z[7usize]);
        external_linear_lazy(&mut state);
        full_round_m31_constants_packed(full_round_m31_constants(state,
                EXTERNAL_INITIAL[0]), EXTERNAL_INITIAL[1])
    }
    #[inline(always)]
    fn interpolate_three_constant_limb(weight0: u32, weight1: u32,
        weight2: u32, constant0: u32, constant1: u32, constant2: u32) -> M31 {
        M31::reduce_u64(u64::from(weight0) * u64::from(constant0) +
                    u64::from(weight1) * u64::from(constant1) +
                u64::from(weight2) * u64::from(constant2))
    }
    #[inline(always)]
    fn interpolate_three_constant_columns(weights: [QM31; 3],
        column0: [u32; 16], column1: [u32; 16], column2: [u32; 16])
        -> [QM31; 16] {
        let mut output = [QM31::ZERO; 16];
        output[0] =
            interpolate_column227(weights, column0[0], column1[0],
                column2[0]);
        output[1] =
            interpolate_column227(weights, column0[1], column1[1],
                column2[1]);
        output[2] =
            interpolate_column227(weights, column0[2], column1[2],
                column2[2]);
        output[3] =
            interpolate_column227(weights, column0[3], column1[3],
                column2[3]);
        output[4] =
            interpolate_column227(weights, column0[4], column1[4],
                column2[4]);
        output[5] =
            interpolate_column227(weights, column0[5], column1[5],
                column2[5]);
        output[6] =
            interpolate_column227(weights, column0[6], column1[6],
                column2[6]);
        output[7] =
            interpolate_column227(weights, column0[7], column1[7],
                column2[7]);
        output[8] =
            interpolate_column227(weights, column0[8], column1[8],
                column2[8]);
        output[9] =
            interpolate_column227(weights, column0[9], column1[9],
                column2[9]);
        output[10] =
            interpolate_column227(weights, column0[10], column1[10],
                column2[10]);
        output[11] =
            interpolate_column227(weights, column0[11], column1[11],
                column2[11]);
        output[12] =
            interpolate_column227(weights, column0[12], column1[12],
                column2[12]);
        output[13] =
            interpolate_column227(weights, column0[13], column1[13],
                column2[13]);
        output[14] =
            interpolate_column227(weights, column0[14], column1[14],
                column2[14]);
        output[15] =
            interpolate_column227(weights, column0[15], column1[15],
                column2[15]);
        output
    }
    fn interpolated_full_pair(state: [QM31; POSEIDON2_WIDTH],
        local: &[QM31; 16]) -> [QM31; POSEIDON2_WIDTH] {
        let weights = [local[1], local[9], local[10]];
        let even =
            interpolate_three_constant_columns(weights, EXTERNAL_INITIAL[2],
                EXTERNAL_FINAL[0], EXTERNAL_FINAL[2]);
        let odd =
            interpolate_three_constant_columns(weights, EXTERNAL_INITIAL[3],
                EXTERNAL_FINAL[1], EXTERNAL_FINAL[3]);
        full_round(full_round(state, even), odd)
    }
    fn interpolated_full_pair_packed(state: [QM31; POSEIDON2_WIDTH],
        local: &[QM31; 16]) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        let weights = [local[1], local[9], local[10]];
        let even =
            interpolate_three_constant_columns(weights, EXTERNAL_INITIAL[2],
                EXTERNAL_FINAL[0], EXTERNAL_FINAL[2]);
        let odd =
            interpolate_three_constant_columns(weights, EXTERNAL_INITIAL[3],
                EXTERNAL_FINAL[1], EXTERNAL_FINAL[3]);
        full_round_packed(full_round(state, even), odd)
    }
    fn interpolated_internal_pair(state: [QM31; POSEIDON2_WIDTH],
        local: &[QM31; 16]) -> [QM31; POSEIDON2_WIDTH] {
        const ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];
        let weights =
            [local[2usize], local[3usize], local[4usize], local[5usize],
                    local[6usize], local[7usize], local[8usize]];
        let even_constants =
            [M31(INTERNAL[2 * (2usize - 2)]), M31(INTERNAL[2 * (3usize - 2)]),
                    M31(INTERNAL[2 * (4usize - 2)]),
                    M31(INTERNAL[2 * (5usize - 2)]),
                    M31(INTERNAL[2 * (6usize - 2)]),
                    M31(INTERNAL[2 * (7usize - 2)]),
                    M31(INTERNAL[2 * (8usize - 2)])];
        let odd_constants =
            [M31(INTERNAL[2 * (2usize - 2) + 1]),
                    M31(INTERNAL[2 * (3usize - 2) + 1]),
                    M31(INTERNAL[2 * (4usize - 2) + 1]),
                    M31(INTERNAL[2 * (5usize - 2) + 1]),
                    M31(INTERNAL[2 * (6usize - 2) + 1]),
                    M31(INTERNAL[2 * (7usize - 2) + 1]),
                    M31(INTERNAL[2 * (8usize - 2) + 1])];
        let even = qm31_m31_dot(&weights, &even_constants);
        let odd = qm31_m31_dot(&weights, &odd_constants);
        internal_round(internal_round(state, even), odd)
    }
    /// Evaluate the four injectively packed successor-state constraints.
    ///
    /// On an active Boolean row the result is zero exactly when the state at
    /// `succ(z)` is the output of the row's two pinned Poseidon rounds (including
    /// row zero's absorption and leading external layer).  No intermediate-round
    /// state is constrained or committed.
    #[inline(never)]
    pub fn evaluate_state_only_poseidon_oracle(openings:
            &StateOnlyPoseidonOpenings,
        selectors: &StateOnlyPoseidonSelectors)
        -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        let leading_low = selectors.local[0];
        let full_low =
            QM31::ZERO.add(selectors.local[1]).add(selectors.local[9]).add(selectors.local[10]);
        let internal_low =
            QM31::ZERO.add(selectors.local[2]).add(selectors.local[3]).add(selectors.local[4]).add(selectors.local[5]).add(selectors.local[6]).add(selectors.local[7]).add(selectors.local[8]);
        let active_low = leading_low.add(full_low).add(internal_low);
        let leading = leading_pair(openings);
        let full = interpolated_full_pair(openings.z, &selectors.local);
        let internal =
            interpolated_internal_pair(openings.z, &selectors.local);
        let weights =
            [active_low, leading_low.neg(), full_low.neg(),
                    internal_low.neg()];
        {
            let mut output =
                [{
                            let group = 0usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let leading =
                                    qm31_pack_base4(&[leading[start + 0], leading[start + 1],
                                                    leading[start + 2], leading[start + 3]]);
                                let full =
                                    qm31_pack_base4(&[full[start + 0], full[start + 1],
                                                    full[start + 2], full[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                selectors.block.mul(qm31_sum_products4([target, leading,
                                                full, internal], weights))
                            }
                        },
                        {
                            let group = 1usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let leading =
                                    qm31_pack_base4(&[leading[start + 0], leading[start + 1],
                                                    leading[start + 2], leading[start + 3]]);
                                let full =
                                    qm31_pack_base4(&[full[start + 0], full[start + 1],
                                                    full[start + 2], full[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                selectors.block.mul(qm31_sum_products4([target, leading,
                                                full, internal], weights))
                            }
                        },
                        {
                            let group = 2usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let leading =
                                    qm31_pack_base4(&[leading[start + 0], leading[start + 1],
                                                    leading[start + 2], leading[start + 3]]);
                                let full =
                                    qm31_pack_base4(&[full[start + 0], full[start + 1],
                                                    full[start + 2], full[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                selectors.block.mul(qm31_sum_products4([target, leading,
                                                full, internal], weights))
                            }
                        },
                        {
                            let group = 3usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let leading =
                                    qm31_pack_base4(&[leading[start + 0], leading[start + 1],
                                                    leading[start + 2], leading[start + 3]]);
                                let full =
                                    qm31_pack_base4(&[full[start + 0], full[start + 1],
                                                    full[start + 2], full[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                selectors.block.mul(qm31_sum_products4([target, leading,
                                                full, internal], weights))
                            }
                        }];
            output
        }
    }
    /// Exact packed-projection implementation of [`evaluate_state_only_poseidon_oracle`].
    ///
    /// Only the two full/full branches benefit: their second external layer is
    /// consumed through its four packed adjoint functionals.  The internal branch
    /// remains on the original path because a generic adjoint there would replace
    /// additions by sixteen extension-field products.
    #[inline(never)]
    pub fn evaluate_state_only_poseidon_oracle_projected(openings:
            &StateOnlyPoseidonOpenings,
        selectors: &StateOnlyPoseidonSelectors)
        -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        let leading_low = selectors.local[0];
        let full_low =
            QM31::ZERO.add(selectors.local[1]).add(selectors.local[9]).add(selectors.local[10]);
        let internal_low =
            QM31::ZERO.add(selectors.local[2]).add(selectors.local[3]).add(selectors.local[4]).add(selectors.local[5]).add(selectors.local[6]).add(selectors.local[7]).add(selectors.local[8]);
        let leading = leading_pair_packed(openings);
        let full =
            interpolated_full_pair_packed(openings.z, &selectors.local);
        let internal =
            interpolated_internal_pair(openings.z, &selectors.local);
        let prepared_weights =
            [PreparedQm31Multiplier::new(leading_low),
                    PreparedQm31Multiplier::new(full_low),
                    PreparedQm31Multiplier::new(internal_low)];
        let prepared_block = PreparedQm31Multiplier::new(selectors.block);
        {
            let mut output =
                [{
                            let group = 0usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                prepared_block.mul(qm31_sum_products3_prepared(&prepared_weights,
                                        &[target.sub(leading[group]), target.sub(full[group]),
                                                    target.sub(internal)]))
                            }
                        },
                        {
                            let group = 1usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                prepared_block.mul(qm31_sum_products3_prepared(&prepared_weights,
                                        &[target.sub(leading[group]), target.sub(full[group]),
                                                    target.sub(internal)]))
                            }
                        },
                        {
                            let group = 2usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                prepared_block.mul(qm31_sum_products3_prepared(&prepared_weights,
                                        &[target.sub(leading[group]), target.sub(full[group]),
                                                    target.sub(internal)]))
                            }
                        },
                        {
                            let group = 3usize;
                            {
                                let start = 4 * group;
                                let target =
                                    qm31_pack_base4(&[openings.succ_z[start + 0],
                                                    openings.succ_z[start + 1], openings.succ_z[start + 2],
                                                    openings.succ_z[start + 3]]);
                                let internal =
                                    qm31_pack_base4(&[internal[start + 0], internal[start + 1],
                                                    internal[start + 2], internal[start + 3]]);
                                prepared_block.mul(qm31_sum_products3_prepared(&prepared_weights,
                                        &[target.sub(leading[group]), target.sub(full[group]),
                                                    target.sub(internal)]))
                            }
                        }];
            output
        }
    }
    fn raw_limb227(output: usize, a: u64, b: u64, c: u64, d: u64) -> u64 {
        match output {
            0 => 2 * a + 3 * b + c + d,
            1 => a + 2 * b + 3 * c + d,
            2 => a + b + 2 * c + 3 * d,
            3 => 3 * a + b + c + 2 * d,
            _ =>
                ::core::panicking::panic("internal error: entered unreachable code"),
        }
    }
    fn external_group227(state: [QM31; 4]) -> [QM31; 4] {
        let input =
            [extension_limbs(state[0]), extension_limbs(state[1]),
                    extension_limbs(state[2]), extension_limbs(state[3])];
        [extension_from_raw_limbs([{
                                let a = u64::from(input[0][0]);
                                let b = u64::from(input[1][0]);
                                let c = u64::from(input[2][0]);
                                let d = u64::from(input[3][0]);
                                raw_limb227(0, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][1]);
                                let b = u64::from(input[1][1]);
                                let c = u64::from(input[2][1]);
                                let d = u64::from(input[3][1]);
                                raw_limb227(0, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][2]);
                                let b = u64::from(input[1][2]);
                                let c = u64::from(input[2][2]);
                                let d = u64::from(input[3][2]);
                                raw_limb227(0, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][3]);
                                let b = u64::from(input[1][3]);
                                let c = u64::from(input[2][3]);
                                let d = u64::from(input[3][3]);
                                raw_limb227(0, a, b, c, d)
                            }]),
                extension_from_raw_limbs([{
                                let a = u64::from(input[0][0]);
                                let b = u64::from(input[1][0]);
                                let c = u64::from(input[2][0]);
                                let d = u64::from(input[3][0]);
                                raw_limb227(1, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][1]);
                                let b = u64::from(input[1][1]);
                                let c = u64::from(input[2][1]);
                                let d = u64::from(input[3][1]);
                                raw_limb227(1, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][2]);
                                let b = u64::from(input[1][2]);
                                let c = u64::from(input[2][2]);
                                let d = u64::from(input[3][2]);
                                raw_limb227(1, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][3]);
                                let b = u64::from(input[1][3]);
                                let c = u64::from(input[2][3]);
                                let d = u64::from(input[3][3]);
                                raw_limb227(1, a, b, c, d)
                            }]),
                extension_from_raw_limbs([{
                                let a = u64::from(input[0][0]);
                                let b = u64::from(input[1][0]);
                                let c = u64::from(input[2][0]);
                                let d = u64::from(input[3][0]);
                                raw_limb227(2, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][1]);
                                let b = u64::from(input[1][1]);
                                let c = u64::from(input[2][1]);
                                let d = u64::from(input[3][1]);
                                raw_limb227(2, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][2]);
                                let b = u64::from(input[1][2]);
                                let c = u64::from(input[2][2]);
                                let d = u64::from(input[3][2]);
                                raw_limb227(2, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][3]);
                                let b = u64::from(input[1][3]);
                                let c = u64::from(input[2][3]);
                                let d = u64::from(input[3][3]);
                                raw_limb227(2, a, b, c, d)
                            }]),
                extension_from_raw_limbs([{
                                let a = u64::from(input[0][0]);
                                let b = u64::from(input[1][0]);
                                let c = u64::from(input[2][0]);
                                let d = u64::from(input[3][0]);
                                raw_limb227(3, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][1]);
                                let b = u64::from(input[1][1]);
                                let c = u64::from(input[2][1]);
                                let d = u64::from(input[3][1]);
                                raw_limb227(3, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][2]);
                                let b = u64::from(input[1][2]);
                                let c = u64::from(input[2][2]);
                                let d = u64::from(input[3][2]);
                                raw_limb227(3, a, b, c, d)
                            },
                            {
                                let a = u64::from(input[0][3]);
                                let b = u64::from(input[1][3]);
                                let c = u64::from(input[2][3]);
                                let d = u64::from(input[3][3]);
                                raw_limb227(3, a, b, c, d)
                            }])]
    }
    fn global_sums227(state: [QM31; 16]) -> [[u64; 4]; 4] {
        [[u64::from(extension_limbs(state[0])[0]) +
                                    u64::from(extension_limbs(state[4])[0]) +
                                u64::from(extension_limbs(state[8])[0]) +
                            u64::from(extension_limbs(state[12])[0]),
                        u64::from(extension_limbs(state[0])[1]) +
                                    u64::from(extension_limbs(state[4])[1]) +
                                u64::from(extension_limbs(state[8])[1]) +
                            u64::from(extension_limbs(state[12])[1]),
                        u64::from(extension_limbs(state[0])[2]) +
                                    u64::from(extension_limbs(state[4])[2]) +
                                u64::from(extension_limbs(state[8])[2]) +
                            u64::from(extension_limbs(state[12])[2]),
                        u64::from(extension_limbs(state[0])[3]) +
                                    u64::from(extension_limbs(state[4])[3]) +
                                u64::from(extension_limbs(state[8])[3]) +
                            u64::from(extension_limbs(state[12])[3])],
                [u64::from(extension_limbs(state[1])[0]) +
                                    u64::from(extension_limbs(state[5])[0]) +
                                u64::from(extension_limbs(state[9])[0]) +
                            u64::from(extension_limbs(state[13])[0]),
                        u64::from(extension_limbs(state[1])[1]) +
                                    u64::from(extension_limbs(state[5])[1]) +
                                u64::from(extension_limbs(state[9])[1]) +
                            u64::from(extension_limbs(state[13])[1]),
                        u64::from(extension_limbs(state[1])[2]) +
                                    u64::from(extension_limbs(state[5])[2]) +
                                u64::from(extension_limbs(state[9])[2]) +
                            u64::from(extension_limbs(state[13])[2]),
                        u64::from(extension_limbs(state[1])[3]) +
                                    u64::from(extension_limbs(state[5])[3]) +
                                u64::from(extension_limbs(state[9])[3]) +
                            u64::from(extension_limbs(state[13])[3])],
                [u64::from(extension_limbs(state[2])[0]) +
                                    u64::from(extension_limbs(state[6])[0]) +
                                u64::from(extension_limbs(state[10])[0]) +
                            u64::from(extension_limbs(state[14])[0]),
                        u64::from(extension_limbs(state[2])[1]) +
                                    u64::from(extension_limbs(state[6])[1]) +
                                u64::from(extension_limbs(state[10])[1]) +
                            u64::from(extension_limbs(state[14])[1]),
                        u64::from(extension_limbs(state[2])[2]) +
                                    u64::from(extension_limbs(state[6])[2]) +
                                u64::from(extension_limbs(state[10])[2]) +
                            u64::from(extension_limbs(state[14])[2]),
                        u64::from(extension_limbs(state[2])[3]) +
                                    u64::from(extension_limbs(state[6])[3]) +
                                u64::from(extension_limbs(state[10])[3]) +
                            u64::from(extension_limbs(state[14])[3])],
                [u64::from(extension_limbs(state[3])[0]) +
                                    u64::from(extension_limbs(state[7])[0]) +
                                u64::from(extension_limbs(state[11])[0]) +
                            u64::from(extension_limbs(state[15])[0]),
                        u64::from(extension_limbs(state[3])[1]) +
                                    u64::from(extension_limbs(state[7])[1]) +
                                u64::from(extension_limbs(state[11])[1]) +
                            u64::from(extension_limbs(state[15])[1]),
                        u64::from(extension_limbs(state[3])[2]) +
                                    u64::from(extension_limbs(state[7])[2]) +
                                u64::from(extension_limbs(state[11])[2]) +
                            u64::from(extension_limbs(state[15])[2]),
                        u64::from(extension_limbs(state[3])[3]) +
                                    u64::from(extension_limbs(state[7])[3]) +
                                u64::from(extension_limbs(state[11])[3]) +
                            u64::from(extension_limbs(state[15])[3])]]
    }
    fn add_global227(value: QM31, sums: [u64; 4]) -> QM31 {
        let limbs = extension_limbs(value);
        extension_from_raw_limbs([u64::from(limbs[0]) + sums[0],
                    u64::from(limbs[1]) + sums[1],
                    u64::from(limbs[2]) + sums[2],
                    u64::from(limbs[3]) + sums[3]])
    }
    fn interpolate_column227(weights: [QM31; 3], column0: u32, column1: u32,
        column2: u32) -> QM31 {
        QM31 {
            c0: CM31::new(interpolate_three_constant_limb(weights[0].c0.a.0,
                    weights[1].c0.a.0, weights[2].c0.a.0, column0, column1,
                    column2),
                interpolate_three_constant_limb(weights[0].c0.b.0,
                    weights[1].c0.b.0, weights[2].c0.b.0, column0, column1,
                    column2)),
            c1: CM31::new(interpolate_three_constant_limb(weights[0].c1.a.0,
                    weights[1].c1.a.0, weights[2].c1.a.0, column0, column1,
                    column2),
                interpolate_three_constant_limb(weights[0].c1.b.0,
                    weights[1].c1.b.0, weights[2].c1.b.0, column0, column1,
                    column2)),
        }
    }
    fn internal_sum227(mut part_sum: [u64; 4], value: QM31) -> [u64; 4] {
        let limbs = extension_limbs(value);
        part_sum[0] += u64::from(limbs[0]);
        part_sum[1] += u64::from(limbs[1]);
        part_sum[2] += u64::from(limbs[2]);
        part_sum[3] += u64::from(limbs[3]);
        part_sum
    }
    fn internal_full_sum227(part_sum: [u64; 4], old_zero: [u32; 4])
        -> [u64; 4] {
        [part_sum[0] + u64::from(old_zero[0]),
                part_sum[1] + u64::from(old_zero[1]),
                part_sum[2] + u64::from(old_zero[2]),
                part_sum[3] + u64::from(old_zero[3])]
    }
    fn internal_zero227(part_sum: [u64; 4], old_zero: [u32; 4]) -> QM31 {
        extension_from_raw_limbs([part_sum[0] + u64::from(P) -
                        u64::from(old_zero[0]),
                    part_sum[1] + u64::from(P) - u64::from(old_zero[1]),
                    part_sum[2] + u64::from(P) - u64::from(old_zero[2]),
                    part_sum[3] + u64::from(P) - u64::from(old_zero[3])])
    }
    fn internal_shift227(value: QM31, full_sum: [u64; 4], shift: u8) -> QM31 {
        let limbs = extension_limbs(value);
        extension_from_raw_limbs([full_sum[0] +
                        (u64::from(limbs[0]) << shift),
                    full_sum[1] + (u64::from(limbs[1]) << shift),
                    full_sum[2] + (u64::from(limbs[2]) << shift),
                    full_sum[3] + (u64::from(limbs[3]) << shift)])
    }
}

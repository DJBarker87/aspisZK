//! Isolated research wire and direct-query schedule for V8-A100/22.
//!
//! This module is not reachable from a deployed instruction.  It deliberately
//! reuses V7's complete C1/C2 query records while changing the profile binding,
//! fixed-field count, query count, and query derivation.  In particular, V8 has
//! one direct bounded sample and no prover-selectable counter or compact-
//! frontier candidate loop.

use crate::field::QM31;
use crate::transcript::Transcript;
use crate::v6_onefold::{
    binary_frontier_nodes, packed_qm31_at, validate_packed_m31, V6WireError, V6_C1_LIMBS_PER_QUERY,
    V6_C1_PACKED_BYTES_PER_QUERY, V6_C2_LIMBS_PER_QUERY, V6_C2_PACKED_BYTES_PER_QUERY,
    V6_FIXED_QM31_VALUES, V6_OOD_QM31_OFFSET, V6_WORK_NONCE_BYTES,
};
use crate::v7_onefold::{V7_COMPACT_DIGEST_BYTES, V7_COMPACT_PRIVATE_SALT_BYTES};

pub const V8_A100_QUERY_COUNT: usize = 22;
pub const V8_A100_TREE_DEPTH: u8 = 18;
pub const V8_A100_DOMAIN_SIZE: u32 = 1 << V8_A100_TREE_DEPTH;
pub const V8_A100_COMPONENTS: usize = 29;
pub const V8_A100_OOD_POINTS: usize = 2;
pub const V8_A100_MAX_QUERY_DRAWS: usize = 64;
pub const V8_A100_DIGEST_BYTES: usize = V7_COMPACT_DIGEST_BYTES;
pub const V8_A100_FRONTIER_MAX_PER_TREE: usize = 296;

/// V6 carries two scalar OOD values. V8 replaces those values with two
/// component-wise vectors of 29 QM31 values each.
pub const V8_A100_FIXED_QM31_VALUES: usize =
    V6_FIXED_QM31_VALUES - 2 + V8_A100_OOD_POINTS * V8_A100_COMPONENTS;
pub const V8_A100_COMPONENT_VECTOR_QM31_OFFSET: usize = V6_OOD_QM31_OFFSET;
pub const V8_A100_RELATION_QM31_OFFSET: usize =
    V8_A100_COMPONENT_VECTOR_QM31_OFFSET + V8_A100_OOD_POINTS * V8_A100_COMPONENTS;
pub const V8_A100_FIXED_M31_LIMBS: usize = 4 * V8_A100_FIXED_QM31_VALUES;
pub const V8_A100_FIXED_PACKED_FIELD_BYTES: usize = (V8_A100_FIXED_M31_LIMBS * 31 + 7) / 8;
pub const V8_A100_C1_BYTES_PER_QUERY: usize = V6_C1_PACKED_BYTES_PER_QUERY;
pub const V8_A100_C2_BYTES_PER_QUERY: usize = V6_C2_PACKED_BYTES_PER_QUERY;
pub const V8_A100_PRIVATE_SALT_BYTES: usize = V7_COMPACT_PRIVATE_SALT_BYTES;
pub const V8_A100_QUERY_BYTES: usize =
    V8_A100_C1_BYTES_PER_QUERY + V8_A100_C2_BYTES_PER_QUERY + V8_A100_PRIVATE_SALT_BYTES;
pub const V8_A100_QUERY_SECTION_BYTES: usize = V8_A100_QUERY_COUNT * V8_A100_QUERY_BYTES;
pub const V8_A100_ROOT_BYTES: usize = 2 * V8_A100_DIGEST_BYTES;
pub const V8_A100_BODY_WITHOUT_FRONTIERS: usize = V8_A100_FIXED_PACKED_FIELD_BYTES
    + V8_A100_ROOT_BYTES
    + V6_WORK_NONCE_BYTES
    + V8_A100_QUERY_SECTION_BYTES;
pub const V8_A100_MAX_BODY_BYTES: usize =
    V8_A100_BODY_WITHOUT_FRONTIERS + 2 * V8_A100_FRONTIER_MAX_PER_TREE * V8_A100_DIGEST_BYTES;

/// Byte-level research profile record.  Byte 28 is the selector-stream count
/// and byte 29 is the candidate count; both are zero.  Byte 30 fixes the
/// bounded direct sampler at 64 draws.
pub const V8_A100_PROFILE_BINDING: [u8; 32] = [
    b'A', b'V', b'8', b'A', b'1', b'0', b'0', b'1', 26, 3, 10, 22, 0x28, 0x01, 26, 32, 29, 2, 3,
    35, 31, 34, 0x71, 0xf1, 0xb9, 0x02, 10, 18, 0, 0, 64, 2,
];

// Source-tied arithmetic: changes to the V6/V7 production wire constants
// break compilation here instead of silently changing the research report.
const _: () = assert!(V6_FIXED_QM31_VALUES == 641);
const _: () = assert!(V8_A100_FIXED_QM31_VALUES == 697);
const _: () = assert!(V8_A100_COMPONENT_VECTOR_QM31_OFFSET == 359);
const _: () = assert!(V8_A100_RELATION_QM31_OFFSET == 417);
const _: () = assert!(V8_A100_FIXED_PACKED_FIELD_BYTES == 10_804);
const _: () = assert!(V8_A100_C1_BYTES_PER_QUERY == 403);
const _: () = assert!(V8_A100_C2_BYTES_PER_QUERY == 186);
const _: () = assert!(V8_A100_QUERY_BYTES == 621);
const _: () = assert!(V8_A100_BODY_WITHOUT_FRONTIERS == 24_542);
const _: () = assert!(V8_A100_MAX_BODY_BYTES == 39_934);

/// Exact maximum of a minimal binary authentication frontier for `query_count`
/// leaves in a depth-`depth` complete tree.
///
/// If `m = ceil(log2(query_count))`, the maximum is
/// `query_count * (depth - m) + (2^m - query_count)`.  The accompanying Lean
/// development proves the recurrence and this closed form; this executable
/// copy is used for source assertions and parameter sweeps.
pub const fn maximum_binary_frontier(depth: u8, query_count: usize) -> usize {
    assert!(query_count > 0);
    assert!(query_count <= (1usize << depth));
    let mut m = 0usize;
    let mut power = 1usize;
    while power < query_count {
        power *= 2;
        m += 1;
    }
    query_count * (depth as usize - m) + (power - query_count)
}

const _: () = assert!(maximum_binary_frontier(18, 22) == V8_A100_FRONTIER_MAX_PER_TREE);

/// A lexicographically stable q22 fixture attaining the depth-18 maximum.
pub const V8_A100_MAX_FRONTIER_FIXTURE: [u32; V8_A100_QUERY_COUNT] = [
    0, 16_384, 32_768, 49_152, 65_536, 81_920, 98_304, 114_688, 131_072, 147_456, 163_840, 172_032,
    180_224, 188_416, 196_608, 204_800, 212_992, 221_184, 229_376, 237_568, 245_760, 253_952,
];

#[derive(Clone)]
pub struct V8A100QuerySchedule {
    pub queries: [u32; V8_A100_QUERY_COUNT],
    pub frontier_nodes: usize,
    pub transcript_state: [u8; 32],
    pub continuation: Transcript,
}

/// Validate a proof-carried or fixture schedule using the exact production
/// frontier routine.  Duplicates and out-of-range positions are rejected.
pub fn validate_v8_a100_schedule(
    queries: [u32; V8_A100_QUERY_COUNT],
) -> Result<usize, V6WireError> {
    let frontier_nodes = binary_frontier_nodes(queries, V8_A100_TREE_DEPTH)?;
    if frontier_nodes > V8_A100_FRONTIER_MAX_PER_TREE {
        return Err(V6WireError::FrontierTooLarge);
    }
    Ok(frontier_nodes)
}

/// Derive V8's sole q22 schedule directly from the current Fiat-Shamir state.
///
/// The caller must already have absorbed [`V8_A100_PROFILE_BINDING`] and the
/// complete prefix.  There is no candidate-domain record, counter, cloned
/// retry branch, or prover choice.  On sampler exhaustion the proof rejects.
pub fn derive_v8_a100_queries(transcript: &Transcript) -> Result<V8A100QuerySchedule, V6WireError> {
    let mut continuation = transcript.clone();
    let queries: [u32; V8_A100_QUERY_COUNT] = continuation
        .challenge_queries_without_replacement(
            V8_A100_QUERY_COUNT,
            V8_A100_DOMAIN_SIZE,
            V8_A100_MAX_QUERY_DRAWS,
        )
        .map_err(|_| V6WireError::InvalidQuerySchedule)?
        .try_into()
        .map_err(|_| V6WireError::InvalidQuerySchedule)?;
    let frontier_nodes = validate_v8_a100_schedule(queries)?;
    Ok(V8A100QuerySchedule {
        queries,
        frontier_nodes,
        transcript_state: continuation.diagnostic_state(),
        continuation,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V8A100QueryRecord<'a> {
    pub c1_packed: &'a [u8],
    pub c2_packed: &'a [u8],
    pub salt: &'a [u8; V8_A100_PRIVATE_SALT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V8A100Wire<'a> {
    pub fixed_fields_packed: &'a [u8],
    pub c1_root: &'a [u8; V8_A100_DIGEST_BYTES],
    pub c2_root: &'a [u8; V8_A100_DIGEST_BYTES],
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V8A100Wire<'a> {
    pub fn parse_for_schedule(
        bytes: &'a [u8],
        queries: [u32; V8_A100_QUERY_COUNT],
        claimed_frontier_nodes: usize,
    ) -> Result<Self, V6WireError> {
        let derived = validate_v8_a100_schedule(queries)?;
        if derived != claimed_frontier_nodes {
            return Err(V6WireError::InvalidQuerySchedule);
        }
        let wire = Self::parse_deferred_canonicality(bytes, derived)?;
        validate_packed_m31(wire.fixed_fields_packed, V8_A100_FIXED_M31_LIMBS)?;
        for ordinal in 0..V8_A100_QUERY_COUNT {
            let query = wire
                .query(ordinal)
                .ok_or(V6WireError::InvalidQuerySchedule)?;
            validate_packed_m31(query.c1_packed, V6_C1_LIMBS_PER_QUERY)?;
            validate_packed_m31(query.c2_packed, V6_C2_LIMBS_PER_QUERY)?;
        }
        Ok(wire)
    }

    pub fn parse_deferred_canonicality(
        bytes: &'a [u8],
        frontier_nodes: usize,
    ) -> Result<Self, V6WireError> {
        if frontier_nodes > V8_A100_FRONTIER_MAX_PER_TREE {
            return Err(V6WireError::FrontierTooLarge);
        }
        let frontier_bytes = frontier_nodes
            .checked_mul(V8_A100_DIGEST_BYTES)
            .ok_or(V6WireError::WrongLength)?;
        let expected = V8_A100_BODY_WITHOUT_FRONTIERS
            .checked_add(2 * frontier_bytes)
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected {
            return Err(V6WireError::WrongLength);
        }
        let (fixed_fields_packed, rest) = bytes.split_at(V8_A100_FIXED_PACKED_FIELD_BYTES);
        if fixed_fields_packed.last().copied().unwrap_or_default() & 0xf0 != 0 {
            return Err(V6WireError::NonCanonicalM31);
        }
        let (c1_root, rest) = rest.split_at(V8_A100_DIGEST_BYTES);
        let (c2_root, rest) = rest.split_at(V8_A100_DIGEST_BYTES);
        let (work_nonces, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V8_A100_QUERY_SECTION_BYTES);
        let (c1_frontier, c2_frontier) = rest.split_at(frontier_bytes);
        Ok(Self {
            fixed_fields_packed,
            c1_root: c1_root.try_into().map_err(|_| V6WireError::WrongLength)?,
            c2_root: c2_root.try_into().map_err(|_| V6WireError::WrongLength)?,
            work_nonces: work_nonces
                .try_into()
                .map_err(|_| V6WireError::WrongLength)?,
            query_section,
            c1_frontier,
            c2_frontier,
        })
    }

    pub fn query(&self, ordinal: usize) -> Option<V8A100QueryRecord<'a>> {
        if ordinal >= V8_A100_QUERY_COUNT {
            return None;
        }
        let start = ordinal * V8_A100_QUERY_BYTES;
        let c1_end = start + V8_A100_C1_BYTES_PER_QUERY;
        let c2_end = c1_end + V8_A100_C2_BYTES_PER_QUERY;
        let end = c2_end + V8_A100_PRIVATE_SALT_BYTES;
        Some(V8A100QueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }

    /// Decode the two component-wise pre-gamma OOD vectors from the exact
    /// fixed-field positions which replace V6's two scalar OOD values.
    /// Canonicality is established by `parse_for_schedule` before this view
    /// can be used by an accepting verifier path.
    pub fn component_ood_vectors(
        &self,
    ) -> Option<[[QM31; V8_A100_COMPONENTS]; V8_A100_OOD_POINTS]> {
        let mut vectors = [[QM31::ZERO; V8_A100_COMPONENTS]; V8_A100_OOD_POINTS];
        for (sample, vector) in vectors.iter_mut().enumerate() {
            for (component, value) in vector.iter_mut().enumerate() {
                let index =
                    V8_A100_COMPONENT_VECTOR_QM31_OFFSET + sample * V8_A100_COMPONENTS + component;
                *value = packed_qm31_at(self.fixed_fields_packed, index)?;
            }
        }
        Some(vectors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::label;
    use crate::v7_onefold::V7_COMPACT_PROFILE_BINDING;
    use alloc::vec;
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn zero_hash(_inputs: &[&[u8]]) -> [u8; 32] {
        [0u8; 32]
    }

    fn seeded_transcript(profile: &[u8]) -> Transcript {
        let mut transcript = Transcript::new(test_hash);
        transcript.absorb(label::PROFILE, profile);
        transcript.absorb(label::STATEMENT, &[0xa1; 32]);
        transcript
    }

    #[test]
    fn exact_wire_arithmetic_is_source_tied() {
        assert_eq!(&V8_A100_PROFILE_BINDING[..8], b"AV8A1001");
        assert_eq!(V8_A100_PROFILE_BINDING[28..30], [0, 0]);
        assert_eq!(V8_A100_FIXED_QM31_VALUES, 697);
        assert_eq!(V8_A100_FIXED_PACKED_FIELD_BYTES, 10_804);
        assert_eq!(V8_A100_QUERY_BYTES, 621);
        assert_eq!(V8_A100_QUERY_SECTION_BYTES, 13_662);
        assert_eq!(V8_A100_BODY_WITHOUT_FRONTIERS, 24_542);
        assert_eq!(V8_A100_MAX_BODY_BYTES, 39_934);
    }

    #[test]
    fn maximum_frontier_fixture_attains_296() {
        assert_eq!(maximum_binary_frontier(18, 22), 296);
        assert_eq!(
            binary_frontier_nodes(V8_A100_MAX_FRONTIER_FIXTURE, 18).unwrap(),
            296
        );
    }

    #[test]
    fn direct_schedule_known_answer_and_continuation() {
        let transcript = seeded_transcript(&V8_A100_PROFILE_BINDING);
        let selected = derive_v8_a100_queries(&transcript).unwrap();
        assert_eq!(
            selected.queries,
            [
                231_696, 190_946, 246_950, 53_197, 7_289, 54_330, 114_496, 152_078, 187_153,
                79_950, 88_748, 246_054, 172_132, 101_489, 123_716, 95_860, 205_063, 89_983,
                87_425, 129_527, 252_951, 48_626,
            ]
        );
        assert_eq!(
            selected.transcript_state,
            selected.continuation.diagnostic_state()
        );
        assert_eq!(
            validate_v8_a100_schedule(selected.queries).unwrap(),
            selected.frontier_nodes
        );
    }

    #[test]
    fn profile_domain_separates_v8_from_v7() {
        let v8 = derive_v8_a100_queries(&seeded_transcript(&V8_A100_PROFILE_BINDING)).unwrap();
        let v7_prefix = seeded_transcript(&V7_COMPACT_PROFILE_BINDING);
        let mut direct_v7_prefix = v7_prefix.clone();
        let v7_queries = direct_v7_prefix
            .challenge_queries_without_replacement(
                V8_A100_QUERY_COUNT,
                V8_A100_DOMAIN_SIZE,
                V8_A100_MAX_QUERY_DRAWS,
            )
            .unwrap();
        assert_ne!(v8.queries.as_slice(), v7_queries.as_slice());
        assert_ne!(v8.transcript_state, direct_v7_prefix.diagnostic_state());
    }

    #[test]
    fn duplicate_and_out_of_range_schedules_reject() {
        let mut duplicate = V8_A100_MAX_FRONTIER_FIXTURE;
        duplicate[21] = duplicate[20];
        assert_eq!(
            validate_v8_a100_schedule(duplicate),
            Err(V6WireError::InvalidQuerySchedule)
        );
        let mut out_of_range = V8_A100_MAX_FRONTIER_FIXTURE;
        out_of_range[21] = V8_A100_DOMAIN_SIZE;
        assert_eq!(
            validate_v8_a100_schedule(out_of_range),
            Err(V6WireError::InvalidQuerySchedule)
        );
    }

    #[test]
    fn direct_sampler_exhaustion_rejects() {
        let mut transcript = Transcript::new(zero_hash);
        transcript.absorb(label::PROFILE, &V8_A100_PROFILE_BINDING);
        assert!(matches!(
            derive_v8_a100_queries(&transcript),
            Err(V6WireError::InvalidQuerySchedule)
        ));
    }

    #[test]
    fn parser_derives_frontier_and_rejects_malformed_lengths() {
        let body = vec![0u8; V8_A100_MAX_BODY_BYTES];
        let wire = V8A100Wire::parse_for_schedule(
            &body,
            V8_A100_MAX_FRONTIER_FIXTURE,
            V8_A100_FRONTIER_MAX_PER_TREE,
        )
        .unwrap();
        assert_eq!(wire.query(21).unwrap().c1_packed.len(), 403);
        assert_eq!(wire.query(21).unwrap().c2_packed.len(), 186);
        assert_eq!(wire.c1_frontier.len(), 296 * 26);
        assert_eq!(wire.c2_frontier.len(), 296 * 26);

        assert!(matches!(
            V8A100Wire::parse_for_schedule(
                &body,
                V8_A100_MAX_FRONTIER_FIXTURE,
                V8_A100_FRONTIER_MAX_PER_TREE - 1,
            ),
            Err(V6WireError::InvalidQuerySchedule)
        ));
        assert!(matches!(
            V8A100Wire::parse_deferred_canonicality(&body[..body.len() - 1], 296),
            Err(V6WireError::WrongLength)
        ));
        assert!(matches!(
            V8A100Wire::parse_deferred_canonicality(&body, 297),
            Err(V6WireError::FrontierTooLarge)
        ));
    }
}

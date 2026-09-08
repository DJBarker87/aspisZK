//! Local-validator-only measurement of the two bounded V7 CU tails.
//!
//! This entrypoint is mutually exclusive with every production dispatcher.
//! It calls the real transcript sampler and the source-visible query sorting
//! routines with adversarial successful inputs. The custom transcript hashes
//! still execute the real SHA syscall before returning controlled bytes, so
//! their extra framing work makes the measured retry delta conservative.

use aspis_core::{
    field::{P, QM31},
    transcript::{label, Transcript},
    v6_onefold::{binary_frontier_nodes, sort_v7_query_order_source_bounded, V6_QUERY_COUNT},
    v7_merkle208::{verify_two_minimal_subtrees_v7_bytes, V7Digest, V7_MERKLE_DIGEST_BYTES},
};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    log::{sol_log_compute_units, sol_log_data},
    program_error::ProgramError,
    pubkey::Pubkey,
};

pub const V7_CU_TAIL_QM31_MIN_TAG: u8 = 78;
pub const V7_CU_TAIL_QM31_MAX_TAG: u8 = 79;
pub const V7_CU_TAIL_QUERY_ASCENDING_TAG: u8 = 80;
pub const V7_CU_TAIL_QUERY_DESCENDING_TAG: u8 = 81;
pub const V7_CU_TAIL_COUNTER_ZERO_TAG: u8 = 82;
pub const V7_CU_TAIL_COUNTER_TWENTY_TAG: u8 = 83;
pub const V7_CU_TAIL_FRONTIER_199_TAG: u8 = 84;
pub const V7_CU_TAIL_FRONTIER_203_TAG: u8 = 85;
pub const V7_CU_TAIL_QUERY_WIRE_BYTES: usize = 1 + V6_QUERY_COUNT * 4;

const DOM_SQUEEZE: u8 = 0x01;
const DOM_ADVANCE: u8 = 0x02;
const FRONTIER_199_QUERIES: [u32; V6_QUERY_COUNT] = [
    18_701, 25_197, 25_596, 45_585, 69_339, 88_051, 97_189, 97_953, 138_390, 180_356, 188_970,
    215_416, 215_695, 216_447, 217_464, 229_382,
];
const FRONTIER_203_QUERIES: [u32; V6_QUERY_COUNT] = [
    29_821, 61_979, 69_179, 75_514, 78_071, 108_705, 108_897, 137_697, 164_485, 165_174, 180_606,
    181_291, 199_267, 201_660, 205_421, 222_926,
];

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_v7_cu_tail_probe_instruction);

fn framed_state<'a>(inputs: &'a [&'a [u8]], domain: u8) -> Option<&'a [u8]> {
    match inputs {
        [state, frame] if state.len() == 32 && *frame == [domain] => Some(*state),
        [packed] if packed.len() == 33 && packed[32] == domain => Some(&packed[..32]),
        _ => None,
    }
}

fn real_hash_then_minimum_block(inputs: &[&[u8]]) -> [u8; 32] {
    let real = crate::verify::sbf_hashv(inputs);
    if framed_state(inputs, DOM_SQUEEZE).is_none() {
        return real;
    }
    let mut block = [0u8; 32];
    for (index, word) in block.chunks_exact_mut(4).enumerate() {
        word.copy_from_slice(&((index + 1) as u32).to_le_bytes());
    }
    block
}

fn real_hash_then_minimum_query_block(inputs: &[&[u8]]) -> [u8; 32] {
    let real = crate::verify::sbf_hashv(inputs);
    match inputs {
        [packed] if packed.len() >= 34 && packed[32] == 0 => [0u8; 32],
        _ => {
            if let Some(state) = framed_state(inputs, DOM_ADVANCE) {
                let mut next = [0u8; 32];
                next[0] = state[0].saturating_add(8);
                next
            } else if let Some(state) = framed_state(inputs, DOM_SQUEEZE) {
                let mut block = [0u8; 32];
                for (index, word) in block.chunks_exact_mut(4).enumerate() {
                    word.copy_from_slice(&(u32::from(state[0]) + index as u32).to_le_bytes());
                }
                block
            } else {
                real
            }
        }
    }
}

fn controlled_maximum_block(inputs: &[&[u8]], accepted_word: u32) -> [u8; 32] {
    let real = crate::verify::sbf_hashv(inputs);
    if let Some(state) = framed_state(inputs, DOM_ADVANCE) {
        let mut next = [0u8; 32];
        next[0] = state[0].saturating_add(1);
        return next;
    }
    if framed_state(inputs, DOM_SQUEEZE).is_none() {
        return real;
    }
    let mut block = [0u8; 32];
    for word in block.chunks_exact_mut(4).take(7) {
        word.copy_from_slice(&P.to_le_bytes());
    }
    block[28..32].copy_from_slice(&accepted_word.to_le_bytes());
    block
}

fn real_hash_then_maximum_nonzero_block(inputs: &[&[u8]]) -> [u8; 32] {
    let accepted = framed_state(inputs, DOM_SQUEEZE)
        .map(|state| u32::from(state[0] >= 8))
        .unwrap_or(1);
    controlled_maximum_block(inputs, accepted)
}

fn real_hash_then_maximum_secure_block(inputs: &[&[u8]]) -> [u8; 32] {
    let accepted = framed_state(inputs, DOM_SQUEEZE)
        .map(|state| u32::from(state[0] >= 8))
        .unwrap_or(1);
    controlled_maximum_block(inputs, accepted)
}

fn real_hash_then_maximum_ordinary_block(inputs: &[&[u8]]) -> [u8; 32] {
    controlled_maximum_block(inputs, 1)
}

fn mix_qm31(sink: &mut [u8; 16], value: QM31) {
    let mut bytes = [0u8; 16];
    value.write_le_bytes(&mut bytes);
    for (left, right) in sink.iter_mut().zip(bytes) {
        *left ^= right;
    }
}

fn run_qm31_minimum_topology() -> Result<[u8; 16], ProgramError> {
    let mut sink = [0u8; 16];
    let mut direct = Transcript::new(real_hash_then_minimum_block);
    for _ in 0..30 {
        mix_qm31(
            &mut sink,
            direct
                .challenge_qm31()
                .map_err(|_| ProgramError::InvalidArgument)?,
        );
    }
    for _ in 0..4 {
        let mut transcript = Transcript::new(real_hash_then_minimum_block);
        mix_qm31(
            &mut sink,
            transcript
                .challenge_nonzero_qm31()
                .map_err(|_| ProgramError::InvalidArgument)?,
        );
    }
    for _ in 0..2 {
        let mut transcript = Transcript::new(real_hash_then_minimum_block);
        let point = transcript
            .challenge_secure_circle_point()
            .map_err(|_| ProgramError::InvalidArgument)?;
        mix_qm31(&mut sink, point.x);
        mix_qm31(&mut sink, point.y);
    }
    Ok(sink)
}

fn run_qm31_maximum_successful_topology() -> Result<[u8; 16], ProgramError> {
    let mut sink = [0u8; 16];
    let mut direct = Transcript::new(real_hash_then_maximum_ordinary_block);
    for _ in 0..30 {
        mix_qm31(
            &mut sink,
            direct
                .challenge_qm31()
                .map_err(|_| ProgramError::InvalidArgument)?,
        );
    }
    for _ in 0..4 {
        let mut transcript = Transcript::new(real_hash_then_maximum_nonzero_block);
        mix_qm31(
            &mut sink,
            transcript
                .challenge_nonzero_qm31()
                .map_err(|_| ProgramError::InvalidArgument)?,
        );
    }
    for _ in 0..2 {
        let mut transcript = Transcript::new(real_hash_then_maximum_secure_block);
        let point = transcript
            .challenge_secure_circle_point()
            .map_err(|_| ProgramError::InvalidArgument)?;
        mix_qm31(&mut sink, point.x);
        mix_qm31(&mut sink, point.y);
    }
    Ok(sink)
}

fn parse_queries(instruction_data: &[u8], descending: bool) -> Result<[u32; 16], ProgramError> {
    if instruction_data.len() != V7_CU_TAIL_QUERY_WIRE_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut queries = [0u32; V6_QUERY_COUNT];
    for (index, output) in queries.iter_mut().enumerate() {
        let offset = 1 + index * 4;
        *output = u32::from_le_bytes(
            instruction_data[offset..offset + 4]
                .try_into()
                .map_err(|_| ProgramError::InvalidInstructionData)?,
        );
    }
    if descending {
        queries.reverse();
    }
    Ok(queries)
}

fn run_query_topology(queries: [u32; 16]) -> Result<[u8; 16], ProgramError> {
    let mut sink = [0u8; 16];
    for candidate in 0..21u32 {
        let frontier =
            binary_frontier_nodes(queries, 18).map_err(|_| ProgramError::InvalidInstructionData)?;
        sink[(candidate as usize) & 15] ^= frontier as u8;
    }
    let mut order: [(u32, usize); V6_QUERY_COUNT] =
        core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
    sort_v7_query_order_source_bounded(&mut order);
    for (index, (query, ordinal)) in order.into_iter().enumerate() {
        sink[index] ^= (query as u8).wrapping_add(ordinal as u8);
    }
    Ok(sink)
}

fn run_q16_candidate_topology(candidate_count: u8) -> Result<[u8; 16], ProgramError> {
    if candidate_count == 0 || candidate_count > 21 {
        return Err(ProgramError::InvalidArgument);
    }
    let transcript = Transcript::new(real_hash_then_minimum_query_block);
    let mut sink = [0u8; 16];
    for counter in 0..candidate_count {
        let mut candidate = transcript.clone();
        candidate.absorb(label::V7_QUERY_CANDIDATE, &[counter]);
        let queries: [u32; V6_QUERY_COUNT] = candidate
            .challenge_queries_without_replacement(V6_QUERY_COUNT, 1 << 18, 64)
            .map_err(|_| ProgramError::InvalidArgument)?
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        sink[usize::from(counter) & 15] ^=
            binary_frontier_nodes(queries, 18).map_err(|_| ProgramError::InvalidArgument)? as u8;
    }
    Ok(sink)
}

fn run_frontier_topology(queries: [u32; 16], frontier_nodes: usize) -> [u8; 16] {
    let zero = [0u8; V7_MERKLE_DIGEST_BYTES];
    let entries: Vec<(u32, V7Digest, V7Digest)> = queries
        .into_iter()
        .map(|query| (query, zero, zero))
        .collect();
    let frontier = vec![0u8; frontier_nodes * V7_MERKLE_DIGEST_BYTES];
    let mut level = Vec::with_capacity(V6_QUERY_COUNT);
    let mut next = Vec::with_capacity(V6_QUERY_COUNT);
    let matched = verify_two_minimal_subtrees_v7_bytes(
        crate::verify::sbf_hashv,
        (&zero, &zero),
        18,
        &entries,
        (&frontier, &frontier),
        &mut level,
        &mut next,
    );
    let mut sink = [0u8; 16];
    sink[0] = u8::from(matched);
    sink[1..9].copy_from_slice(&(frontier_nodes as u64).to_le_bytes());
    sink
}

pub fn process_v7_cu_tail_probe_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    if !accounts.is_empty() {
        return Err(ProgramError::InvalidArgument);
    }
    let tag = instruction_data
        .first()
        .copied()
        .ok_or(ProgramError::InvalidInstructionData)?;
    sol_log_compute_units();
    let sink = match tag {
        V7_CU_TAIL_QM31_MIN_TAG if instruction_data.len() == 1 => run_qm31_minimum_topology()?,
        V7_CU_TAIL_QM31_MAX_TAG if instruction_data.len() == 1 => {
            run_qm31_maximum_successful_topology()?
        }
        V7_CU_TAIL_QUERY_ASCENDING_TAG => {
            run_query_topology(parse_queries(instruction_data, false)?)?
        }
        V7_CU_TAIL_QUERY_DESCENDING_TAG => {
            run_query_topology(parse_queries(instruction_data, true)?)?
        }
        V7_CU_TAIL_COUNTER_ZERO_TAG if instruction_data.len() == 1 => {
            run_q16_candidate_topology(1)?
        }
        V7_CU_TAIL_COUNTER_TWENTY_TAG if instruction_data.len() == 1 => {
            run_q16_candidate_topology(21)?
        }
        V7_CU_TAIL_FRONTIER_199_TAG if instruction_data.len() == 1 => {
            run_frontier_topology(FRONTIER_199_QUERIES, 199)
        }
        V7_CU_TAIL_FRONTIER_203_TAG if instruction_data.len() == 1 => {
            run_frontier_topology(FRONTIER_203_QUERIES, 203)
        }
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    sol_log_data(&[b"aspis-v7-cu-tail-probe-v1", &sink]);
    sol_log_compute_units();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adversarial_qm31_topologies_are_successful() {
        assert!(run_qm31_minimum_topology().is_ok());
        assert!(run_qm31_maximum_successful_topology().is_ok());
    }

    #[test]
    fn query_orders_have_identical_semantics() {
        let queries: [u32; 16] = core::array::from_fn(|index| index as u32);
        let mut reversed = queries;
        reversed.reverse();
        assert_eq!(
            binary_frontier_nodes(queries, 18),
            binary_frontier_nodes(reversed, 18)
        );
        assert!(run_query_topology(queries).is_ok());
        assert!(run_query_topology(reversed).is_ok());
    }

    #[test]
    fn controlled_q16_candidates_use_exactly_two_blocks() {
        assert!(run_q16_candidate_topology(1).is_ok());
        assert!(run_q16_candidate_topology(21).is_ok());
    }

    #[test]
    fn frontier_probe_queries_have_pinned_counts() {
        assert_eq!(binary_frontier_nodes(FRONTIER_199_QUERIES, 18), Ok(199));
        assert_eq!(binary_frontier_nodes(FRONTIER_203_QUERIES, 18), Ok(203));
    }
}

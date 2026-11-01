//! Allocation-bounded selected terminal for the eight-lane Pool V1 pair
//! forest. The relation keeps the frozen Tag-73 three-opening geometry and
//! packs Poseidon, 94 semantic source lanes and the 136-link Copy argument
//! into the same 29 theta lanes as the one-tree payment terminal.


// Closure-free array construction, evaluated in increasing source index order.
macro_rules! qm31_array {
    (4, $index:ident, $body:expr) => {{
        let mut output=[QM31::ZERO;4];
        { let $index=0usize; output[0]=$body; }
        { let $index=1usize; output[1]=$body; }
        { let $index=2usize; output[2]=$body; }
        { let $index=3usize; output[3]=$body; }
        output
    }};

    (16, $index:ident, $body:expr) => {{
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
        { let $index=15usize; output[15]=$body; }
        output
    }};

    ($n:expr, $index:ident, $body:expr) => {{
        let mut output = [QM31::ZERO; $n];
        let mut $index = 0usize;
        while $index < $n {
            output[$index] = $body;
            $index += 1;
        }
        output
    }};
}

use crate::host_terminal_field::{qm31_pack_base4, PreparedQm31Multiplier};
use aspis_core::{
    field::{CM31, M31, QM31},
    state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
};

use aspis_statement::{
    poseidon2::{Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_WIDTH, RATE},
    state_only_poseidon::{
        StateOnlyPoseidonOpenings,
        StateOnlyPoseidonSelectors,
    },
};

use aspis_statement::pool_v1::{
    pair_tree_profile::{PoolV1PairLatePublicStatementV1, POOL_V1_PAIR_CAPACITY},
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
};

use aspis_prover::host_arithmetic::state_only_selected_mask_value;
use crate::reference_copy_terminal::{evaluate_with_selectors,PoolV1PairForestCompiledVariantV1,Selectors};

const DOMAIN_OWNER_KEY:M31=M31(0x4153_0001);
const DOMAIN_NULLIFIER:M31=M31(0x4153_0002);
const DOMAIN_NOTE:M31=M31(0x4153_0003);

pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1: usize = 1024;
pub const POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1: usize = 16;
pub const POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1: usize = 3;
pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1: usize =
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1: usize =
    POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1 * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1;
pub const POOL_V1_PAIR_FOREST_SOURCE_SEMANTIC_LANES_V1: usize = 94;
pub const POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1: usize = 24;
pub const POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1: usize = 4;
pub const POOL_V1_PAIR_FOREST_COPY_LANES_V1: usize = 1;
pub const POOL_V1_PAIR_FOREST_THETA_LANES_V1: usize = POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1
    + POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1
    + POOL_V1_PAIR_FOREST_COPY_LANES_V1;
pub const POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1: usize =
    POOL_V1_PAIR_FOREST_THETA_LANES_V1 - 1;
pub const POOL_V1_PAIR_FOREST_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE_V1: usize = 26;
pub const POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1: usize = 27;
pub const POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1: usize = 27;
pub const POOL_V1_PAIR_FOREST_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
    if cfg!(feature = "optimized-terminal") {
        2
    } else {
        1
    };
pub const POOL_V1_PAIR_FOREST_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
    core::mem::size_of::<Selectors>();

const SELECTED_H1_COLUMN: usize =
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
const VALUE_AUXILIARY_BLOCK: usize = 63;
const INPUT_OCCUPANCY_ROW: usize = 63 * 16 + 9;
const OUTPUT_OCCUPANCY_ROW: usize = 63 * 16 + 10;

const _: () = assert!(DIGEST_ELEMS == 8);
const _: () = assert!(POSEIDON2_WIDTH == 16);
const _: () = assert!(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28);
const _: () = assert!(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84);
const _: () = assert!(POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29);
const _: () = assert!(POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28);

mod constants {
    include!("host_terminal_constants.rs");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestSemanticTerminalErrorV1 {
    InvalidPublicAmount,
    InvalidAppendTransition,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompiledVariant {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy)]
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

#[inline(always)]
fn lift_m31(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

/// Count only the trailing one bits used by the twenty-level append tree.
/// The bounded form is equivalent to capping u64::trailing_ones at twenty.
fn bounded_append_carry(mut index: u64) -> usize {
    let mut carry = 0usize;
    while carry < 20 {
        if index & 1 == 0 {
            return carry;
        }
        index >>= 1u32;
        carry += 1;
    }
    carry
}

#[inline(always)]
fn add_preweighted<const N: usize>(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    start: usize,
    values: &[QM31; N],
) {
    let first = start / 4;
    let last = (start + N - 1) / 4;
    let mut group_index = first; while group_index <= last { let group=group_index; group_index+=1;
        let lanes: [QM31; 4] = qm31_array!(4, slot, {
            let source = 4 * group + slot;
            if source >= start && source < start + N {
                values[source - start]
            } else {
                QM31::ZERO
            }
        });
        packed[group] = packed[group].add(qm31_pack_base4(&lanes));
    }
}

/// Exact linear factoring for a contiguous source-lane interval with one
/// common selector:
///
/// `pack(s*r0, ..., s*r3) = s*pack(r0, ..., r3)`.
///
/// The global source offset may be unaligned, so the first and last groups
/// retain the same zero padding as `add_preweighted`.
#[inline(always)]
#[cfg(any(test, feature = "optimized-terminal"))]
fn add_preweighted_shared_selector<const N: usize>(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    start: usize,
    values: &[QM31; N],
    selector: QM31,
) {
    let first = start / 4;
    let last = (start + N - 1) / 4;
    let mut group_index = first; while group_index <= last { let group=group_index; group_index+=1;
        let lanes: [QM31; 4] = qm31_array!(4, slot, {
            let source = 4 * group + slot;
            if source >= start && source < start + N {
                values[source - start]
            } else {
                QM31::ZERO
            }
        });
        packed[group] = packed[group].add(selector.mul(qm31_pack_base4(&lanes)));
    }
}

#[inline(always)]
fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>]) -> QM31 {
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

fn validate_transition(
    public: SemanticPublic,
) -> Result<(), PoolV1PairForestSemanticTerminalErrorV1> {
    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    if source.pool != public.pool
        || source.deployment_domain != public.deployment_domain
        || source.sequence != source.next_pair_index
        || source.next_pair_index >= POOL_V1_PAIR_CAPACITY
        || checked_next227(source.next_pair_index,after.next_pair_index)
    {
        return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
    }
    let index = source.next_pair_index;
    let carry = bounded_append_carry(index);
    let mut level_index = 0usize; while level_index < 20 { let level=level_index; level_index+=1;
        if level == carry && carry < 20 {
            continue;
        }
        let expected = if level < carry || ((index >> level) & 1) == 0 {
            empty_root(level)
        } else {
            digest227(source.frontier,level)
        };
        if digest227(after.next_frontier,level) != expected {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
        }
    }
    Ok(())
}

fn poseidon_selectors(selectors: &Selectors) -> StateOnlyPoseidonSelectors {
    StateOnlyPoseidonSelectors {
        block: sum_interval227(selectors.high,QM31::ZERO,0,57),
        local: selectors.low,
    }
}

#[inline(never)]
fn initial_variant_selectors(
    variant: CompiledVariant,
    high27: QM31,
    high28: QM31,
    high29: QM31,
) -> (QM31, QM31, QM31, QM31) {
    match variant {
        CompiledVariant::PrivateTransfer => (
            high27,
            QM31::ZERO,
            high27.add(high28),
            high29,
        ),
        CompiledVariant::Withdrawal => (
            QM31::ZERO,
            high27.add(high28).add(high29),
            QM31::ZERO,
            QM31::ZERO,
        ),
    }
}

fn semantic_initial_and_absorption(
    public: SemanticPublic,
    openings: StateOnlyPoseidonOpenings,
    selectors: Selectors,
) -> ([QM31; 16], [QM31; 16]) {
    let nodes = sum_interval227(selectors.high,sum_interval227(selectors.high,QM31::ZERO,4,25),33,57);
    let first_common = selectors.high[0]
        .add(selectors.high[1])
        .add(selectors.high[25])
        .add(selectors.high[30]);
    let (transfer_first, fixed, private_chunk_eight, private_chunk_two) =
        initial_variant_selectors(
            public.variant,
            selectors.high[27],
            selectors.high[28],
            selectors.high[29],
        );
    let full_initial_selector = selectors.low[0].mul(first_common.add(transfer_first).add(fixed));
    let rate_initial_selector = selectors.low[0].mul(nodes);
    let full = PreparedQm31Multiplier::new(full_initial_selector);
    let full_or_rate =
        PreparedQm31Multiplier::new(full_initial_selector.add(rate_initial_selector));
    let mut initial = qm31_array!(16, lane, {
        initial_lane227(lane,full_or_rate,full,read227(openings.z,lane))
    });
    let note_first = selectors.high[1]
        .add(selectors.high[30])
        .add(transfer_first);
    let domain = selectors.high[0]
        .mul_m31(DOMAIN_OWNER_KEY)
        .add(note_first.mul_m31(DOMAIN_NOTE))
        .add(selectors.high[25].mul_m31(DOMAIN_NULLIFIER));
    let length = selectors.high[0]
        .mul_m31(M31(8))
        .add(note_first.mul_m31(M31(18)))
        .add(selectors.high[25].mul_m31(M31(16)));
    initial[RATE] = initial[RATE].sub(selectors.low[0].mul(domain));
    initial[RATE + 1] = initial[RATE + 1].sub(selectors.low[0].mul(length));

    let mut chunk_eight = selectors.high[0]
        .add(selectors.high[1])
        .add(selectors.high[2])
        .add(selectors.high[25])
        .add(selectors.high[26])
        .add(selectors.high[30])
        .add(selectors.high[31]);
    let mut chunk_two = selectors.high[3].add(selectors.high[32]);
    chunk_eight = chunk_eight.add(private_chunk_eight);
    chunk_two = chunk_two.add(private_chunk_two);
    #[cfg(not(feature = "optimized-terminal"))]
    let absorption = absorption_lanes_literal(
        selectors.low[12],
        fixed,
        chunk_two,
        chunk_eight,
        nodes,
        &openings.z,
    );
    #[cfg(feature = "optimized-terminal")]
    let absorption = absorption_lanes_factored(
        selectors.low[12],
        fixed,
        chunk_two,
        chunk_eight,
        nodes,
        &openings.z,
    );
    (initial, absorption)
}

#[cfg(any(test, not(feature = "optimized-terminal")))]
fn absorption_lanes_literal(
    low: QM31,
    fixed: QM31,
    chunk_two: QM31,
    chunk_eight: QM31,
    nodes: QM31,
    openings: &[QM31; 16],
) -> [QM31; 16] {
    qm31_array!(16, lane, {
        absorption_lane227(lane,low,fixed,chunk_two,chunk_eight,nodes,read227(*openings,lane))
    })
}

#[cfg(any(test, feature = "optimized-terminal"))]
fn absorption_lanes_factored(
    low: QM31,
    fixed: QM31,
    chunk_two: QM31,
    chunk_eight: QM31,
    nodes: QM31,
    openings: &[QM31; 16],
) -> [QM31; 16] {
    let scales = [
        PreparedQm31Multiplier::new(low.mul(fixed)),
        PreparedQm31Multiplier::new(low.mul(fixed.add(chunk_two))),
        PreparedQm31Multiplier::new(low.mul(fixed.add(chunk_two).add(chunk_eight).add(nodes))),
    ];
    qm31_array!(16, lane, {
        let scale = if lane < 2 {
            scales[0]
        } else if lane < RATE {
            scales[1]
        } else {
            scales[2]
        };
        scale.mul(openings[lane])
    })
}

#[inline(always)]
#[cfg(any(test, not(feature = "optimized-terminal")))]
fn add_digest_binding(
    mut output: [QM31; DIGEST_ELEMS],
    selector: QM31,
    opened: [QM31; POSEIDON2_WIDTH],
    start: usize,
    expected: Digest,
    right_tweak: bool,
) -> [QM31;DIGEST_ELEMS] {
    let mut lane_index = 0usize;  
        let target=tweak227(expected[0usize],right_tweak,0usize);
        output[0usize] = output[0usize].add(selector.mul(opened[start + 0usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[1usize],right_tweak,1usize);
        output[1usize] = output[1usize].add(selector.mul(opened[start + 1usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[2usize],right_tweak,2usize);
        output[2usize] = output[2usize].add(selector.mul(opened[start + 2usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[3usize],right_tweak,3usize);
        output[3usize] = output[3usize].add(selector.mul(opened[start + 3usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[4usize],right_tweak,4usize);
        output[4usize] = output[4usize].add(selector.mul(opened[start + 4usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[5usize],right_tweak,5usize);
        output[5usize] = output[5usize].add(selector.mul(opened[start + 5usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[6usize],right_tweak,6usize);
        output[6usize] = output[6usize].add(selector.mul(opened[start + 6usize].sub(lift_m31(target))));
    
 
        let target=tweak227(expected[7usize],right_tweak,7usize);
        output[7usize] = output[7usize].add(selector.mul(opened[start + 7usize].sub(lift_m31(target))));
    
    output
}

#[inline(never)]
fn add_schedule_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let (initial, absorption) = semantic_initial_and_absorption(public, *openings, *selectors);
    add_preweighted(packed, 0, &initial);
    add_preweighted(packed, 16, &absorption);
}

#[inline(never)]
fn add_path_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let path_selector = sum_interval227(selectors.high,QM31::ZERO,57,63).mul(
        selectors.low[1]
            .add(selectors.low[5])
            .add(selectors.low[9])
            .add(selectors.low[13]),
    );
    #[cfg(not(feature = "optimized-terminal"))]
    let path = path_lanes_literal(path_selector, openings);
    #[cfg(feature = "optimized-terminal")]
    let path = path_lanes_factored(path_selector, openings);
    add_preweighted(packed, 32, &path);
}

#[cfg(any(test, not(feature = "optimized-terminal")))]
fn path_lanes_literal(path_selector: QM31, openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
    let bit = openings.z[0];
    let mut path = [QM31::ZERO; 17];
    path[0] = path_selector.mul(bit.mul(bit.sub(QM31::ONE)));
    let mut lane_index = 0usize;  
        let current = openings.z[1 + 0usize];
        path[1 + 0usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[0usize].sub(current));
        path[1 + DIGEST_ELEMS + 0usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 0usize].sub(current));
    
 
        let current = openings.z[1 + 1usize];
        path[1 + 1usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[1usize].sub(current));
        path[1 + DIGEST_ELEMS + 1usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 1usize].sub(current));
    
 
        let current = openings.z[1 + 2usize];
        path[1 + 2usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[2usize].sub(current));
        path[1 + DIGEST_ELEMS + 2usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 2usize].sub(current));
    
 
        let current = openings.z[1 + 3usize];
        path[1 + 3usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[3usize].sub(current));
        path[1 + DIGEST_ELEMS + 3usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 3usize].sub(current));
    
 
        let current = openings.z[1 + 4usize];
        path[1 + 4usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[4usize].sub(current));
        path[1 + DIGEST_ELEMS + 4usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 4usize].sub(current));
    
 
        let current = openings.z[1 + 5usize];
        path[1 + 5usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[5usize].sub(current));
        path[1 + DIGEST_ELEMS + 5usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 5usize].sub(current));
    
 
        let current = openings.z[1 + 6usize];
        path[1 + 6usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[6usize].sub(current));
        path[1 + DIGEST_ELEMS + 6usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 6usize].sub(current));
    
 
        let current = openings.z[1 + 7usize];
        path[1 + 7usize] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[7usize].sub(current));
        path[1 + DIGEST_ELEMS + 7usize] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + 7usize].sub(current));
    
    path
}

#[cfg(any(test, feature = "optimized-terminal"))]
fn path_lanes_factored(path_selector: QM31, openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
    let bit = openings.z[0];
    let selected_bit = path_selector.mul(bit);
    let selected_empty = path_selector.sub(selected_bit);
    let left = PreparedQm31Multiplier::new(selected_empty);
    let right = PreparedQm31Multiplier::new(selected_bit);
    let mut path = [QM31::ZERO; 17];
    path[0] = selected_bit.mul(bit.sub(QM31::ONE));
    let current0 = openings.z[1];
    path[1] = left.mul(openings.succ_z[0].sub(current0));
    path[9] = right.mul(openings.succ_z[RATE].sub(current0));
    let current1 = openings.z[2];
    path[2] = left.mul(openings.succ_z[1].sub(current1));
    path[10] = right.mul(openings.succ_z[RATE + 1].sub(current1));
    let current2 = openings.z[3];
    path[3] = left.mul(openings.succ_z[2].sub(current2));
    path[11] = right.mul(openings.succ_z[RATE + 2].sub(current2));
    let current3 = openings.z[4];
    path[4] = left.mul(openings.succ_z[3].sub(current3));
    path[12] = right.mul(openings.succ_z[RATE + 3].sub(current3));
    let current4 = openings.z[5];
    path[5] = left.mul(openings.succ_z[4].sub(current4));
    path[13] = right.mul(openings.succ_z[RATE + 4].sub(current4));
    let current5 = openings.z[6];
    path[6] = left.mul(openings.succ_z[5].sub(current5));
    path[14] = right.mul(openings.succ_z[RATE + 5].sub(current5));
    let current6 = openings.z[7];
    path[7] = left.mul(openings.succ_z[6].sub(current6));
    path[15] = right.mul(openings.succ_z[RATE + 6].sub(current6));
    let current7 = openings.z[8];
    path[8] = left.mul(openings.succ_z[7].sub(current7));
    path[16] = right.mul(openings.succ_z[RATE + 7].sub(current7));
    path
}

#[inline(never)]
fn add_value_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let value_selectors =
        [selectors.row(16 * VALUE_AUXILIARY_BLOCK),
         selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2),
         selectors.row(16 * VALUE_AUXILIARY_BLOCK + 4)];
    let range_selector = QM31::ZERO
        .add(value_selectors[0])
        .add(value_selectors[1])
        .add(value_selectors[2]);
    let mut range = [QM31::ZERO; 33];
    let mut index = 0usize;
    
        range[0usize] = read227(openings.z,0usize).square().sub(read227(openings.z,0usize));
        
    

        range[1usize] = read227(openings.z,1usize).square().sub(read227(openings.z,1usize));
        
    

        range[2usize] = read227(openings.z,2usize).square().sub(read227(openings.z,2usize));
        
    

        range[3usize] = read227(openings.z,3usize).square().sub(read227(openings.z,3usize));
        
    

        range[4usize] = read227(openings.z,4usize).square().sub(read227(openings.z,4usize));
        
    

        range[5usize] = read227(openings.z,5usize).square().sub(read227(openings.z,5usize));
        
    

        range[6usize] = read227(openings.z,6usize).square().sub(read227(openings.z,6usize));
        
    

        range[7usize] = read227(openings.z,7usize).square().sub(read227(openings.z,7usize));
        
    

        range[8usize] = read227(openings.z,8usize).square().sub(read227(openings.z,8usize));
        
    

        range[9usize] = read227(openings.z,9usize).square().sub(read227(openings.z,9usize));
        
    
    index = 0;
    
        range[10 + 0usize] = read227(openings.succ_z,0usize)
            .square()
            .sub(read227(openings.succ_z,0usize));
        
    

        range[10 + 1usize] = read227(openings.succ_z,1usize)
            .square()
            .sub(read227(openings.succ_z,1usize));
        
    

        range[10 + 2usize] = read227(openings.succ_z,2usize)
            .square()
            .sub(read227(openings.succ_z,2usize));
        
    

        range[10 + 3usize] = read227(openings.succ_z,3usize)
            .square()
            .sub(read227(openings.succ_z,3usize));
        
    

        range[10 + 4usize] = read227(openings.succ_z,4usize)
            .square()
            .sub(read227(openings.succ_z,4usize));
        
    

        range[10 + 5usize] = read227(openings.succ_z,5usize)
            .square()
            .sub(read227(openings.succ_z,5usize));
        
    

        range[10 + 6usize] = read227(openings.succ_z,6usize)
            .square()
            .sub(read227(openings.succ_z,6usize));
        
    

        range[10 + 7usize] = read227(openings.succ_z,7usize)
            .square()
            .sub(read227(openings.succ_z,7usize));
        
    

        range[10 + 8usize] = read227(openings.succ_z,8usize)
            .square()
            .sub(read227(openings.succ_z,8usize));
        
    

        range[10 + 9usize] = read227(openings.succ_z,9usize)
            .square()
            .sub(read227(openings.succ_z,9usize));
        
    
    index = 0;
    
        range[20 + 0usize] = read227(openings.xor12_z,0usize)
            .square()
            .sub(read227(openings.xor12_z,0usize));
        
    

        range[20 + 1usize] = read227(openings.xor12_z,1usize)
            .square()
            .sub(read227(openings.xor12_z,1usize));
        
    

        range[20 + 2usize] = read227(openings.xor12_z,2usize)
            .square()
            .sub(read227(openings.xor12_z,2usize));
        
    

        range[20 + 3usize] = read227(openings.xor12_z,3usize)
            .square()
            .sub(read227(openings.xor12_z,3usize));
        
    

        range[20 + 4usize] = read227(openings.xor12_z,4usize)
            .square()
            .sub(read227(openings.xor12_z,4usize));
        
    

        range[20 + 5usize] = read227(openings.xor12_z,5usize)
            .square()
            .sub(read227(openings.xor12_z,5usize));
        
    

        range[20 + 6usize] = read227(openings.xor12_z,6usize)
            .square()
            .sub(read227(openings.xor12_z,6usize));
        
    

        range[20 + 7usize] = read227(openings.xor12_z,7usize)
            .square()
            .sub(read227(openings.xor12_z,7usize));
        
    

        range[20 + 8usize] = read227(openings.xor12_z,8usize)
            .square()
            .sub(read227(openings.xor12_z,8usize));
        
    

        range[20 + 9usize] = read227(openings.xor12_z,9usize)
            .square()
            .sub(read227(openings.xor12_z,9usize));
        
    
    let reconstructed = reconstruct_10(&openings.z)
        .add(reconstruct_10(&openings.succ_z).mul_m31(M31(1 << 10)))
        .add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 << 20)));
    range[30] = openings.z[10].sub(reconstructed);
    range[31] = openings.succ_z[10];
    range[32] = openings.xor12_z[10];
    #[cfg(not(feature = "optimized-terminal"))]
    {
        let mut residual_index = 0usize;
        
            range[0usize] = range_selector.mul(read227(range,0usize));
            
        

            range[1usize] = range_selector.mul(read227(range,1usize));
            
        

            range[2usize] = range_selector.mul(read227(range,2usize));
            
        

            range[3usize] = range_selector.mul(read227(range,3usize));
            
        

            range[4usize] = range_selector.mul(read227(range,4usize));
            
        

            range[5usize] = range_selector.mul(read227(range,5usize));
            
        

            range[6usize] = range_selector.mul(read227(range,6usize));
            
        

            range[7usize] = range_selector.mul(read227(range,7usize));
            
        

            range[8usize] = range_selector.mul(read227(range,8usize));
            
        

            range[9usize] = range_selector.mul(read227(range,9usize));
            
        

            range[10usize] = range_selector.mul(read227(range,10usize));
            
        

            range[11usize] = range_selector.mul(read227(range,11usize));
            
        

            range[12usize] = range_selector.mul(read227(range,12usize));
            
        

            range[13usize] = range_selector.mul(read227(range,13usize));
            
        

            range[14usize] = range_selector.mul(read227(range,14usize));
            
        

            range[15usize] = range_selector.mul(read227(range,15usize));
            
        

            range[16usize] = range_selector.mul(read227(range,16usize));
            
        

            range[17usize] = range_selector.mul(read227(range,17usize));
            
        

            range[18usize] = range_selector.mul(read227(range,18usize));
            
        

            range[19usize] = range_selector.mul(read227(range,19usize));
            
        

            range[20usize] = range_selector.mul(read227(range,20usize));
            
        

            range[21usize] = range_selector.mul(read227(range,21usize));
            
        

            range[22usize] = range_selector.mul(read227(range,22usize));
            
        

            range[23usize] = range_selector.mul(read227(range,23usize));
            
        

            range[24usize] = range_selector.mul(read227(range,24usize));
            
        

            range[25usize] = range_selector.mul(read227(range,25usize));
            
        

            range[26usize] = range_selector.mul(read227(range,26usize));
            
        

            range[27usize] = range_selector.mul(read227(range,27usize));
            
        

            range[28usize] = range_selector.mul(read227(range,28usize));
            
        

            range[29usize] = range_selector.mul(read227(range,29usize));
            
        

            range[30usize] = range_selector.mul(read227(range,30usize));
            
        

            range[31usize] = range_selector.mul(read227(range,31usize));
            
        

            range[32usize] = range_selector.mul(read227(range,32usize));
            
        
        add_preweighted(packed, 49, &range);
    }
    #[cfg(feature = "optimized-terminal")]
    add_preweighted_shared_selector(packed, 49, &range, range_selector);

    let conservation_selector = selectors.row(16 * VALUE_AUXILIARY_BLOCK + 6);
    let conservation = [
        conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
        conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1])),
    ];
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
fn add_occupancy_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let input_occupancy = selectors.row(INPUT_OCCUPANCY_ROW);
    let output_occupancy = selectors.row(OUTPUT_OCCUPANCY_ROW);
    let expected_output = variant_expected_output(public.variant);
    #[cfg(not(feature = "optimized-terminal"))]
    let occupancy = occupancy_lanes_literal(
        input_occupancy,
        output_occupancy,
        expected_output,
        &openings.z,
    );
    #[cfg(feature = "optimized-terminal")]
    let occupancy = occupancy_lanes_factored(
        input_occupancy,
        output_occupancy,
        expected_output,
        &openings.z,
    );
    add_preweighted(packed, 0, &occupancy);
}

#[cfg(any(test, not(feature = "optimized-terminal")))]
fn occupancy_lanes_literal(
    input_occupancy: QM31,
    output_occupancy: QM31,
    expected_output: M31,
    opened: &[QM31; 16],
) -> [QM31; 12] {
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
    
    occupancy[11] = input_occupancy
        .mul(opened[10].mul(one_minus))
        .add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
    occupancy
}

#[cfg(any(test, feature = "optimized-terminal"))]
fn occupancy_lanes_factored(
    input_occupancy: QM31,
    output_occupancy: QM31,
    expected_output: M31,
    opened: &[QM31; 16],
) -> [QM31; 12] {
    let occupied = opened[0];
    let inverse = opened[1];
    let one_minus = QM31::ONE.sub(occupied);
    let both = input_occupancy.add(output_occupancy);
    let occupied_selector = both.mul(occupied);
    let empty_selector = both.sub(occupied_selector);
    let empty = PreparedQm31Multiplier::new(empty_selector);
    let mut occupancy = [QM31::ZERO; 12];
    occupancy[0] = occupied_selector.mul(occupied.sub(QM31::ONE));
    occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
    occupancy[2] = empty.mul(inverse);
    let mut lane_index = 0usize;  
        occupancy[3 + 0usize] = empty.mul(opened[2 + 0usize]);
    
 
        occupancy[3 + 1usize] = empty.mul(opened[2 + 1usize]);
    
 
        occupancy[3 + 2usize] = empty.mul(opened[2 + 2usize]);
    
 
        occupancy[3 + 3usize] = empty.mul(opened[2 + 3usize]);
    
 
        occupancy[3 + 4usize] = empty.mul(opened[2 + 4usize]);
    
 
        occupancy[3 + 5usize] = empty.mul(opened[2 + 5usize]);
    
 
        occupancy[3 + 6usize] = empty.mul(opened[2 + 6usize]);
    
 
        occupancy[3 + 7usize] = empty.mul(opened[2 + 7usize]);
    
    occupancy[11] = input_occupancy
        .mul(opened[10].mul(one_minus))
        .add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
    occupancy
}

#[inline(never)]
#[cfg(any(test, not(feature = "optimized-terminal")))]
fn public_digest_lanes(
    public: SemanticPublic,
    openings: StateOnlyPoseidonOpenings,
    selectors: Selectors,
) -> [QM31; DIGEST_ELEMS] {
    let mut digests = [QM31::ZERO; DIGEST_ELEMS];
    digests = add_digest_binding(
        digests,
        selectors.row(56 * 16 + 11),
        openings.z,
        0,
        public.anchor,
        false,
    );
    digests = add_digest_binding(
        digests,
        selectors.row(26 * 16 + 11),
        openings.z,
        0,
        public.nullifier,
        false,
    );
    if let Some(recipient) = public.recipient {
        digests = add_digest_binding(
            digests,
            selectors.row(29 * 16 + 11),
            openings.z,
            0,
            recipient,
            false,
        );
    }
    digests = add_digest_binding(
        digests,
        selectors.row(32 * 16 + 11),
        openings.z,
        0,
        public.change,
        false,
    );

    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    let mut level_index = 0usize;  
        let block = 34 + 0usize;
        if ((source.next_pair_index >> 0usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(0usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,0usize),
                false,
            );
        }
    
 
        let block = 34 + 1usize;
        if ((source.next_pair_index >> 1usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(1usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,1usize),
                false,
            );
        }
    
 
        let block = 34 + 2usize;
        if ((source.next_pair_index >> 2usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(2usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,2usize),
                false,
            );
        }
    
 
        let block = 34 + 3usize;
        if ((source.next_pair_index >> 3usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(3usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,3usize),
                false,
            );
        }
    
 
        let block = 34 + 4usize;
        if ((source.next_pair_index >> 4usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(4usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,4usize),
                false,
            );
        }
    
 
        let block = 34 + 5usize;
        if ((source.next_pair_index >> 5usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(5usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,5usize),
                false,
            );
        }
    
 
        let block = 34 + 6usize;
        if ((source.next_pair_index >> 6usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(6usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,6usize),
                false,
            );
        }
    
 
        let block = 34 + 7usize;
        if ((source.next_pair_index >> 7usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(7usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,7usize),
                false,
            );
        }
    
 
        let block = 34 + 8usize;
        if ((source.next_pair_index >> 8usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(8usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,8usize),
                false,
            );
        }
    
 
        let block = 34 + 9usize;
        if ((source.next_pair_index >> 9usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(9usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,9usize),
                false,
            );
        }
    
 
        let block = 34 + 10usize;
        if ((source.next_pair_index >> 10usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(10usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,10usize),
                false,
            );
        }
    
 
        let block = 34 + 11usize;
        if ((source.next_pair_index >> 11usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(11usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,11usize),
                false,
            );
        }
    
 
        let block = 34 + 12usize;
        if ((source.next_pair_index >> 12usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(12usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,12usize),
                false,
            );
        }
    
 
        let block = 34 + 13usize;
        if ((source.next_pair_index >> 13usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(13usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,13usize),
                false,
            );
        }
    
 
        let block = 34 + 14usize;
        if ((source.next_pair_index >> 14usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(14usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,14usize),
                false,
            );
        }
    
 
        let block = 34 + 15usize;
        if ((source.next_pair_index >> 15usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(15usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,15usize),
                false,
            );
        }
    
 
        let block = 34 + 16usize;
        if ((source.next_pair_index >> 16usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(16usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,16usize),
                false,
            );
        }
    
 
        let block = 34 + 17usize;
        if ((source.next_pair_index >> 17usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(17usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,17usize),
                false,
            );
        }
    
 
        let block = 34 + 18usize;
        if ((source.next_pair_index >> 18usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(18usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,18usize),
                false,
            );
        }
    
 
        let block = 34 + 19usize;
        if ((source.next_pair_index >> 19usize) & 1) == 0 {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16),
                openings.z,
                RATE,
                empty_root(19usize),
                true,
            );
        } else {
            digests = add_digest_binding(
                digests,
                selectors.row(block * 16 + 12),
                openings.z,
                0,
                digest227(source.frontier,19usize),
                false,
            );
        }
    
    digests = add_digest_binding(
        digests,
        selectors.row(53 * 16 + 11),
        openings.z,
        0,
        after.next_root,
        false,
    );
    let carry = bounded_append_carry(source.next_pair_index);
    if carry < 20 {
        digests = add_digest_binding(
            digests,
            selectors.row((33 + carry) * 16 + 11),
            openings.z,
            0,
            after.next_frontier[carry],
            false,
        );
    }
    digests
}

/// Audit-only form of `public_digest_lanes` after applying the exact identity
///
/// `pack(s * d0, ..., s * d3) = s * pack(d0, ..., d3)`.
///
/// The two outputs are the unchanged semantic theta lanes 21 and 22.  Keeping
/// the literal evaluator above available to tests makes the source-level
/// equivalence executable for both variants and every selector point.
#[cfg(any(test, feature = "optimized-terminal"))]
#[inline(always)]
fn add_digest_binding_packed(
    output: &mut [QM31; DIGEST_ELEMS / 4],
    selector: QM31,
    opened: &[QM31; POSEIDON2_WIDTH],
    start: usize,
    expected: &Digest,
    right_tweak: bool,
) {
    for group in 0..DIGEST_ELEMS / 4 {
        let residuals: [QM31; 4] = qm31_array!(4, slot, {
            let lane = 4 * group + slot;
            let mut target = expected[lane];
            if right_tweak && lane + 1 == DIGEST_ELEMS {
                target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
            }
            opened[start + lane].sub(lift_m31(target))
        });
        output[group] = output[group].add(selector.mul(qm31_pack_base4(&residuals)));
    }
}

#[cfg(any(
    test,
    all(
        feature = "optimized-terminal",
        not(feature = "optimized-terminal")
    )
))]
#[inline(never)]
fn public_digest_packed_row_major(
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; DIGEST_ELEMS / 4] {
    let mut digests = [QM31::ZERO; DIGEST_ELEMS / 4];
    add_digest_binding_packed(
        &mut digests,
        selectors.row(56 * 16 + 11),
        &openings.z,
        0,
        &public.anchor,
        false,
    );
    add_digest_binding_packed(
        &mut digests,
        selectors.row(26 * 16 + 11),
        &openings.z,
        0,
        &public.nullifier,
        false,
    );
    if let Some(recipient) = public.recipient {
        add_digest_binding_packed(
            &mut digests,
            selectors.row(29 * 16 + 11),
            &openings.z,
            0,
            &recipient,
            false,
        );
    }
    add_digest_binding_packed(
        &mut digests,
        selectors.row(32 * 16 + 11),
        &openings.z,
        0,
        &public.change,
        false,
    );

    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    let mut level_index = 0usize; while level_index < 20 { let level=level_index; level_index+=1;
        let block = 34 + level;
        if ((source.next_pair_index >> level) & 1) == 0 {
            add_digest_binding_packed(
                &mut digests,
                selectors.row(block * 16),
                &openings.z,
                RATE,
                &empty_root(level),
                true,
            );
        } else {
            add_digest_binding_packed(
                &mut digests,
                selectors.row(block * 16 + 12),
                &openings.z,
                0,
                &digest227(source.frontier,level),
                false,
            );
        }
    }
    add_digest_binding_packed(
        &mut digests,
        selectors.row(53 * 16 + 11),
        &openings.z,
        0,
        &after.next_root,
        false,
    );
    let carry = bounded_append_carry(source.next_pair_index);
    if carry < 20 {
        add_digest_binding_packed(
            &mut digests,
            selectors.row((33 + carry) * 16 + 11),
            &openings.z,
            0,
            &after.next_frontier[carry],
            false,
        );
    }
    digests
}

#[cfg(any(
    test,
    feature = "optimized-terminal"
))]
#[inline(always)]
fn left_digest_packed_selector_tensor(
    high: QM31,
    opened: [QM31; POSEIDON2_WIDTH],
    expected: Digest,
) -> [QM31; DIGEST_ELEMS / 4] {
    let prepared_high = PreparedQm31Multiplier::new(high);
    let residual0 = [
        opened[0].sub(lift_m31(expected[0])),
        opened[1].sub(lift_m31(expected[1])),
        opened[2].sub(lift_m31(expected[2])),
        opened[3].sub(lift_m31(expected[3])),
    ];
    let residual1 = [
        opened[4].sub(lift_m31(expected[4])),
        opened[5].sub(lift_m31(expected[5])),
        opened[6].sub(lift_m31(expected[6])),
        opened[7].sub(lift_m31(expected[7])),
    ];
    [
        prepared_high.mul(qm31_pack_base4(&residual0)),
        prepared_high.mul(qm31_pack_base4(&residual1)),
    ]
}

#[cfg(any(
    test,
    feature = "optimized-terminal"
))]
#[inline(never)]
fn optional_recipient_packed_selector_tensor(
    recipient: Option<Digest>,
    opened: [QM31; POSEIDON2_WIDTH],
    high: QM31,
) -> [QM31; DIGEST_ELEMS / 4] {
    match recipient {
        Some(expected) => {
            let prepared_high = PreparedQm31Multiplier::new(high);
            let mut contribution = [QM31::ZERO; DIGEST_ELEMS / 4];
            let mut group = 0usize;
            while group < DIGEST_ELEMS / 4 {
                let lane = 4 * group;
                let residuals = [
                    opened[lane].sub(lift_m31(expected[lane])),
                    opened[lane + 1].sub(lift_m31(expected[lane + 1])),
                    opened[lane + 2].sub(lift_m31(expected[lane + 2])),
                    opened[lane + 3].sub(lift_m31(expected[lane + 3])),
                ];
                contribution[group] = prepared_high.mul(qm31_pack_base4(&residuals));
                group += 1;
            }
            contribution
        }
        None => [QM31::ZERO; DIGEST_ELEMS / 4],
    }
}

#[cfg(any(
    test,
    feature = "optimized-terminal"
))]
#[inline(never)]
fn append_level_packed_selector_tensor(
    next_pair_index: u64,
    level: usize,
    frontier: Digest,
    opened: [QM31; POSEIDON2_WIDTH],
    high: QM31,
) -> (
    [QM31; DIGEST_ELEMS / 4],
    [QM31; DIGEST_ELEMS / 4],
) {
    let prepared_high = PreparedQm31Multiplier::new(high);
    if ((next_pair_index >> level) & 1) == 0 {
        let expected = empty_root(level);
        let residual0 = [
            opened[RATE].sub(lift_m31(expected[0])),
            opened[RATE + 1].sub(lift_m31(expected[1])),
            opened[RATE + 2].sub(lift_m31(expected[2])),
            opened[RATE + 3].sub(lift_m31(expected[3])),
        ];
        let residual1 = [
            opened[RATE + 4].sub(lift_m31(expected[4])),
            opened[RATE + 5].sub(lift_m31(expected[5])),
            opened[RATE + 6].sub(lift_m31(expected[6])),
            opened[RATE + 7]
                .sub(lift_m31(expected[7].add(MERKLE_NODE_COMPRESSION_V3_TWEAK))),
        ];
        (
            [
                prepared_high.mul(qm31_pack_base4(&residual0)),
                prepared_high.mul(qm31_pack_base4(&residual1)),
            ],
            [QM31::ZERO; DIGEST_ELEMS / 4],
        )
    } else {
        let residual0 = [
            opened[0].sub(lift_m31(frontier[0])),
            opened[1].sub(lift_m31(frontier[1])),
            opened[2].sub(lift_m31(frontier[2])),
            opened[3].sub(lift_m31(frontier[3])),
        ];
        let residual1 = [
            opened[4].sub(lift_m31(frontier[4])),
            opened[5].sub(lift_m31(frontier[5])),
            opened[6].sub(lift_m31(frontier[6])),
            opened[7].sub(lift_m31(frontier[7])),
        ];
        (
            [QM31::ZERO; DIGEST_ELEMS / 4],
            [
                prepared_high.mul(qm31_pack_base4(&residual0)),
                prepared_high.mul(qm31_pack_base4(&residual1)),
            ],
        )
    }
}

#[cfg(any(
    test,
    feature = "optimized-terminal"
))]
#[inline(always)]
fn append_levels_packed_selector_tensor(
    next_pair_index: u64,
    frontier: [Digest; 20],
    opened: [QM31; POSEIDON2_WIDTH],
    selector_high: [QM31; 64],
) -> (
    [QM31; DIGEST_ELEMS / 4],
    [QM31; DIGEST_ELEMS / 4],
) {
    let mut local0 = [QM31::ZERO; DIGEST_ELEMS / 4];
    let mut local12 = [QM31::ZERO; DIGEST_ELEMS / 4];
    let mut level = 0usize;
    while level < 20 {
        let (level0, level12) = append_level_packed_selector_tensor(
            next_pair_index,
            level,
            frontier[level],
            opened,
            selector_high[34 + level],
        );
        local0[0] = local0[0].add(level0[0]);
        local0[1] = local0[1].add(level0[1]);
        local12[0] = local12[0].add(level12[0]);
        local12[1] = local12[1].add(level12[1]);
        level += 1;
    }
    (local0, local12)
}

#[cfg(any(
    test,
    feature = "optimized-terminal"
))]
#[inline(never)]
fn optional_carry_packed_selector_tensor(
    carry: usize,
    opened: [QM31; POSEIDON2_WIDTH],
    high: QM31,
    frontier: Digest,
) -> [QM31; DIGEST_ELEMS / 4] {
    if carry < 20 {
        let prepared_high = PreparedQm31Multiplier::new(high);
        let residual0 = [
            opened[0].sub(lift_m31(frontier[0])),
            opened[1].sub(lift_m31(frontier[1])),
            opened[2].sub(lift_m31(frontier[2])),
            opened[3].sub(lift_m31(frontier[3])),
        ];
        let residual1 = [
            opened[4].sub(lift_m31(frontier[4])),
            opened[5].sub(lift_m31(frontier[5])),
            opened[6].sub(lift_m31(frontier[6])),
            opened[7].sub(lift_m31(frontier[7])),
        ];
        [
            prepared_high.mul(qm31_pack_base4(&residual0)),
            prepared_high.mul(qm31_pack_base4(&residual1)),
        ]
    } else {
        [QM31::ZERO; DIGEST_ELEMS / 4]
    }
}

/// Exact selector-tensor form of the packed public digest constraints:
///
/// `sum_e high[b_e] * low[l_e] * residual_e`
///
/// is contracted as
///
/// `sum_l low[l] * (sum_{e:l_e=l} high[b_e] * residual_e)`.
///
/// The frozen binding grammar uses only locals 0, 11 and 12. No row,
/// expected digest, tweak, semantic lane or transcript value changes.
#[cfg(any(
    test,
    feature = "optimized-terminal"
))]
#[inline(never)]
fn public_digest_packed_selector_tensor(
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; DIGEST_ELEMS / 4] {
    let mut local_sums = [[QM31::ZERO; DIGEST_ELEMS / 4]; 3];
    let anchor = left_digest_packed_selector_tensor(
        selectors.high[56],
        openings.z,
        public.anchor,
    );
    local_sums[1][0] = local_sums[1][0].add(anchor[0]);
    local_sums[1][1] = local_sums[1][1].add(anchor[1]);
    let nullifier = left_digest_packed_selector_tensor(
        selectors.high[26],
        openings.z,
        public.nullifier,
    );
    local_sums[1][0] = local_sums[1][0].add(nullifier[0]);
    local_sums[1][1] = local_sums[1][1].add(nullifier[1]);
    let recipient = optional_recipient_packed_selector_tensor(
        public.recipient,
        openings.z,
        selectors.high[29],
    );
    local_sums[1][0] = local_sums[1][0].add(recipient[0]);
    local_sums[1][1] = local_sums[1][1].add(recipient[1]);
    let change = left_digest_packed_selector_tensor(
        selectors.high[32],
        openings.z,
        public.change,
    );
    local_sums[1][0] = local_sums[1][0].add(change[0]);
    local_sums[1][1] = local_sums[1][1].add(change[1]);

    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    let next_pair_index = source.next_pair_index;
    let source_frontier = source.frontier;
    let opened_z = openings.z;
    let selector_high = selectors.high;
    let (append_local0, append_local12) = append_levels_packed_selector_tensor(
        next_pair_index,
        source_frontier,
        opened_z,
        selector_high,
    );
    local_sums[0][0] = local_sums[0][0].add(append_local0[0]);
    local_sums[0][1] = local_sums[0][1].add(append_local0[1]);
    local_sums[2][0] = local_sums[2][0].add(append_local12[0]);
    local_sums[2][1] = local_sums[2][1].add(append_local12[1]);
    let next_root = left_digest_packed_selector_tensor(
        selector_high[53],
        opened_z,
        after.next_root,
    );
    local_sums[1][0] = local_sums[1][0].add(next_root[0]);
    local_sums[1][1] = local_sums[1][1].add(next_root[1]);
    let carry = bounded_append_carry(next_pair_index);
    let carry_index = core::cmp::min(carry, 19);
    let carry_contribution = optional_carry_packed_selector_tensor(
        carry,
        opened_z,
        selector_high[33 + carry_index],
        after.next_frontier[carry_index],
    );
    local_sums[1][0] = local_sums[1][0].add(carry_contribution[0]);
    local_sums[1][1] = local_sums[1][1].add(carry_contribution[1]);

    let mut output = [QM31::ZERO; DIGEST_ELEMS / 4];
    let low0 = PreparedQm31Multiplier::new(selectors.low[0]);
    output[0] = output[0].add(low0.mul(local_sums[0][0]));
    output[1] = output[1].add(low0.mul(local_sums[0][1]));
    let low11 = PreparedQm31Multiplier::new(selectors.low[11]);
    output[0] = output[0].add(low11.mul(local_sums[1][0]));
    output[1] = output[1].add(low11.mul(local_sums[1][1]));
    let low12 = PreparedQm31Multiplier::new(selectors.low[12]);
    output[0] = output[0].add(low12.mul(local_sums[2][0]));
    output[1] = output[1].add(low12.mul(local_sums[2][1]));
    output
}

#[cfg(any(test, feature = "optimized-terminal"))]
#[inline(always)]
fn public_digest_packed(
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; DIGEST_ELEMS / 4] {
    #[cfg(not(feature = "optimized-terminal"))]
    return public_digest_packed_row_major(public, openings, selectors);
    #[cfg(feature = "optimized-terminal")]
    return public_digest_packed_selector_tensor(public, openings, selectors);
}

#[inline(never)]
fn scalar_lanes(
    variant: CompiledVariant,
    withdrawal_amount_present: bool,
    input_asset: QM31,
    mut output_scalar: QM31,
    private_transfer_term: QM31,
    withdrawal_term: QM31,
) -> [QM31; 2] {
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

fn semantic_packed(
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1] {
    let mut packed = [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
    add_schedule_lanes(&mut packed, public, openings, selectors);
    add_path_lanes(&mut packed, openings, selectors);
    add_value_lanes(&mut packed, openings, selectors);
    add_occupancy_lanes(&mut packed, public, openings, selectors);
    #[cfg(not(feature = "optimized-terminal"))]
    add_preweighted(
        &mut packed,
        84,
        &public_digest_lanes(public, *openings, *selectors),
    );
    #[cfg(feature = "optimized-terminal")]
    {
        let digests = public_digest_packed(public, openings, selectors);
        packed[84 / 4] = packed[84 / 4].add(digests[0]);
        packed[84 / 4 + 1] = packed[84 / 4 + 1].add(digests[1]);
    }
    let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
    let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
    let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
    let private_transfer_term = selectors.row(28 * 16 + 12).mul(asset_difference);
    let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
    let withdrawal_term = selectors
        .row(16 * VALUE_AUXILIARY_BLOCK + 2)
        .mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
    let scalars = scalar_lanes(
        public.variant,
        public.withdrawal_amount.is_some(),
        input_asset,
        output_scalar,
        private_transfer_term,
        withdrawal_term,
    );
    add_preweighted(&mut packed, 92, &scalars);
    packed
}

fn selected_claim(
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
    point: usize,
    column: usize,
) -> QM31 {
    claims[point * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 + column]
}

#[inline(never)]
fn copy_variant(variant: CompiledVariant) -> PoolV1PairForestCompiledVariantV1 {
    match variant {
        CompiledVariant::PrivateTransfer => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
        CompiledVariant::Withdrawal => PoolV1PairForestCompiledVariantV1::Withdrawal,
    }
}

fn equality_value(left: &[QM31;10], right: &[QM31;10]) -> QM31 {
    let mut product=equality_factor(left[0],right[0]);
    product=product.mul(equality_factor(left[1],right[1]));
    product=product.mul(equality_factor(left[2],right[2]));
    product=product.mul(equality_factor(left[3],right[3]));
    product=product.mul(equality_factor(left[4],right[4]));
    product=product.mul(equality_factor(left[5],right[5]));
    product=product.mul(equality_factor(left[6],right[6]));
    product=product.mul(equality_factor(left[7],right[7]));
    product=product.mul(equality_factor(left[8],right[8]));
    product=product.mul(equality_factor(left[9],right[9]));
    product
}

#[allow(clippy::type_complexity)]
fn composition_parts(
    public: SemanticPublic,
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<
    (
        QM31,
        [QM31; 16],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
        QM31,
        QM31,
    ),
    PoolV1PairForestSemanticTerminalErrorV1,
> {
    let invalid_amount = match public.withdrawal_amount {
        None => false,
        Some(amount) => amount == 0 || amount >= (1 << 30u32),
    };
    if invalid_amount {
        return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
    }
    validate_transition(public)?;
    let openings = StateOnlyPoseidonOpenings {
        z: select_c1_227(*claims,0),
        succ_z: select_c1_227(*claims,1),
        xor12_z: select_c1_227(*claims,2),
    };
    let mask_only = qm31_array!(STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, column, {
        selected_claim(
            claims,
            0,
            POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column,
        )
    });
    let selectors = Selectors::boxed_at_point(point);
    let poseidon =
        evaluate_state_only_poseidon_oracle_projected(&openings, &poseidon_selectors(&selectors));
    let semantic = semantic_packed(public, &openings, &selectors);
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let copy = evaluate_with_selectors(
        &openings.z,
        h1_z,
        &selectors,
        lambda,
        chi,
        public.transition.live_snapshot.next_pair_index,
        copy_variant(public.variant),
    );
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy.residual;
    let mut index = semantic.len();
    while index > 0 {
        index -= 1;
        composition = prepared_theta.mul(composition).add(read227(semantic,index));
    }
    index = poseidon.len();
    while index > 0 {
        index -= 1;
        composition = prepared_theta.mul(composition).add(read227(poseidon,index));
    }
    Ok((
        composition,
        openings.z,
        mask_only,
        selected_claim(claims, 0, SELECTED_G_COLUMN),
        h1_z,
        copy.active,
    ))
}

fn terminal_parts(
    public: SemanticPublic,
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
) -> Result<
    (
        QM31,
        [QM31; 16],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
    ),
    PoolV1PairForestSemanticTerminalErrorV1,
> {
    let (composition, c1, mask_only, g, h1_z, copy_active) =
        composition_parts(public, claims, point, lambda, chi, theta)?;
    let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z))
        .add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
    Ok((original, c1, mask_only, g))
}

fn private_public<'a>(
    public: &PoolV1PrivateTransferPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic {
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

fn withdrawal_public<'a>(
    public: &PoolV1WithdrawalPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic {
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
    ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty, $convert:ident) => {
        #[allow(clippy::too_many_arguments)]
        pub fn $composition(
            public: &$public_ty,
            transition: &PoolV1PairLatePublicStatementV1,
            claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
        ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
            Ok(composition_parts(
                $convert(public, transition),
                claims,
                point,
                lambda,
                chi,
                theta,
            )?
            .0)
        }

        #[allow(clippy::too_many_arguments)]
        pub fn $unmasked(
            public: &$public_ty,
            transition: &PoolV1PairLatePublicStatementV1,
            claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
            zerocheck_point: &[QM31; 10],
            mu: QM31,
        ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
            Ok(terminal_parts(
                $convert(public, transition),
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )?
            .0)
        }

        #[allow(clippy::too_many_arguments)]
        #[inline(never)]
        pub fn $masked(
            public: &$public_ty,
            transition: &PoolV1PairLatePublicStatementV1,
            claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
            zerocheck_point: &[QM31; 10],
            mu: QM31,
            eta: QM31,
        ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
            let (original, c1, mask_only, g) = terminal_parts(
                $convert(public, transition),
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )?;
            Ok(state_only_selected_mask_value(&c1, &mask_only, g, point).add(eta.mul(original)))
        }
    };
}

define_variant_terminal!(
    evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
    PoolV1PrivateTransferPublicV1,
    private_public
);

define_variant_terminal!(
    evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1,
    PoolV1WithdrawalPublicV1,
    withdrawal_public
);

/// R0's width-29 view of this exact pair-forest terminal. No generic Spend
/// terminal, legacy transcript or legacy claim stride is selected here.
#[cfg(feature = "prover")]
pub mod r0 {
    use super::*;
    use alloc::vec::Vec;
    use aspis_core::field::WideExact;
    use aspis_core::state_only_prefix::r0::{Challenges, Error, PointClaims};

    #[derive(Clone, Copy)]
    pub enum Public<'a> {
        Transfer(
            &'a PoolV1PrivateTransferPublicV1,
            &'a PoolV1PairLatePublicStatementV1,
        ),
        Withdrawal(
            &'a PoolV1WithdrawalPublicV1,
            &'a PoolV1PairLatePublicStatementV1,
        ),
    }
    impl<'a> Public<'a> {
        pub(super) fn semantic(self) -> SemanticPublic {
            match self {
                Self::Transfer(public, transition) => private_public(public, transition),
                Self::Withdrawal(public, transition) => withdrawal_public(public, transition),
            }
        }
        pub fn transition(self) -> &'a PoolV1PairLatePublicStatementV1 {
            match self { Self::Transfer(_, t) | Self::Withdrawal(_, t) => t }
        }
        /// SPEC §9 declaration order. Pool/domain/sequence and source current
        /// root are not fields of R0P.Public and are not silently hashed here.
        /// Existing reject-only public guards remain in the terminal.
        pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
            fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error> {
                for value in values {
                    if value.0 >= aspis_core::field::P {
                        return Err(Error::Public);
                    }
                    out.extend_from_slice(&value.0.to_le_bytes());
                }
                Ok(())
            }
            // The fixed width is checked at both call sites. Explicit calls
            // avoid nested frontier loops during source extraction.
            fn frontier(out: &mut Vec<u8>, values: &[Digest; 20]) -> Result<(), Error> {
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
        pub fn terminal_qm31(
            self,
            claims: &[[QM31; 29]; 3],
            alpha: &[QM31; 10],
            c: &Challenges,
        ) -> Result<QM31, Error> {
            let mut selected=[QM31::ZERO;84];let mut i=0usize;while i<84 {selected[i]=claims[i/28][i%28];i+=1;}
            match terminal_parts(
                self.semantic(),
                &selected,
                alpha,
                c.lambda,
                c.chi,
                c.theta,
                &c.zc,
                c.mu,
            ) {Ok(parts)=>Ok(parts.0),Err(_)=>Err(Error::Public)}
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
        pub fn terminal(
            self,
            claims: &PointClaims,
            alpha: &[QM31; 10],
            c: &Challenges,
        ) -> Result<WideExact, Error> {
            if claims.iter().flatten().all(|x| x.c1() == QM31::ZERO) {
                let values = terminal_values(claims, None);
                return self
                    .terminal_qm31(&values, alpha, c)
                    .map(WideExact::from_qm31);
            }
            let mut total = WideExact::ZERO;
            for i in 0..26u32 {
                let values = terminal_values(claims, Some(M31(i)));
                let value = self.terminal_qm31(&values, alpha, c)?;
                let mut numerator = WideExact::ONE;
                let mut denominator = M31::ONE;
                for j in 0..26u32 {
                    if i == j {
                        continue;
                    }
                    numerator =
                        numerator.mul(WideExact::V.sub(WideExact::from_qm31(lift_m31(M31(j)))));
                    denominator = denominator.mul(M31(i).sub(M31(j)));
                }
                total = total.add(numerator.mul_qm31(value.mul_m31(denominator.inv())));
            }
            Ok(total)
        }
    }
    // Isolate the 87 K values in one small frame; arithmetic is unchanged.
    #[inline(never)]
    fn terminal_values(claims: &PointClaims, t: Option<M31>) -> [[QM31;29];3] {
        let mut values=[[QM31::ZERO;29];3];
        for p in 0..3 {for l in 0..29 {
            let x=claims[p][l];
            values[p][l]=match t {None=>x.c0(),Some(t)=>x.c0().add(x.c1().mul_m31(t))};
        }}
        values
    }

}


#[inline(always)]
fn equality_factor(a: QM31, b: QM31) -> QM31 {
    let ab = a.mul(b);
    QM31::ONE.sub(a).sub(b).add(ab).add(ab)
}

fn claim227(claims: [[QM31;29];3], index: usize) -> QM31 { let row=claims[index/28]; row[index%28] }

/// Owned value entry: copy the immutable inputs before evaluating the same chain.
pub fn reference227(public: SemanticPublic, claims: [[QM31;29];3], alpha: [QM31;10], c: aspis_core::state_only_prefix::r0::Challenges) -> Result<QM31,aspis_core::state_only_prefix::r0::Error> {
    let selected=select227(claims);
    match terminal_parts(public,&selected,&alpha,c.lambda,c.chi,c.theta,&c.zc,c.mu) {
        Ok(parts)=>Ok(parts.0),
        Err(_)=>Err(aspis_core::state_only_prefix::r0::Error::Public)
    }
}

fn read227<const N:usize>(values:[QM31;N], index:usize)->QM31 { values[index] }

fn digest227(values:[Digest;20],index:usize)->Digest { values[index] }

fn sum_interval227(high:[QM31;64], initial:QM31, start:usize, end:usize)->QM31 {
    let mut sum=initial;
    let mut i=start;
    while i<end { sum=sum.add(read227(high,i)); i+=1; }
    sum
}

fn initial_lane227(lane:usize,full_or_rate:PreparedQm31Multiplier,full:PreparedQm31Multiplier,value:QM31)->QM31 {
    if lane<RATE { full_or_rate.mul(value) } else { full.mul(value) }
}

fn tweak227(value:M31,right_tweak:bool,lane:usize)->M31 {
    if right_tweak && lane+1==DIGEST_ELEMS { value.add(MERKLE_NODE_COMPRESSION_V3_TWEAK) } else { value }
}

pub fn select227(claims:[[QM31;29];3])->[QM31;84] {
    let mut selected=[QM31::ZERO;84];
    let mut i=0usize;
    while i<84 { let value=claim227(claims,i); selected[i]=value; i+=1; }
    selected
}

fn absorption_lane227(lane:usize,low:QM31,fixed:QM31,chunk_two:QM31,chunk_eight:QM31,nodes:QM31,opened:QM31)->QM31 {
    let blocks=if lane<2 {fixed} else if lane<RATE {fixed.add(chunk_two)} else {fixed.add(chunk_two).add(chunk_eight).add(nodes)};
    low.mul(blocks).mul(opened)
}

fn checked_next227(index:u64,next:u64)->bool { match index.checked_add(1) { Some(value)=>value!=next,None=>true } }

use crate::reference_poseidon::evaluate_state_only_poseidon_oracle_projected;

pub fn native227(public:r0::Public<'_>,claims:&[[QM31;29];3],alpha:&[QM31;10],c:&aspis_core::state_only_prefix::r0::Challenges)->Result<QM31,aspis_core::state_only_prefix::r0::Error> {
    reference227(public.semantic(),*claims,*alpha,*c)
}

#[inline(never)]
fn select_c1_227(claims:[QM31;84],row:usize)->[QM31;16] {
    [selected_claim(&claims,row,0),selected_claim(&claims,row,1),selected_claim(&claims,row,2),selected_claim(&claims,row,3),selected_claim(&claims,row,4),selected_claim(&claims,row,5),selected_claim(&claims,row,6),selected_claim(&claims,row,7),selected_claim(&claims,row,8),selected_claim(&claims,row,9),selected_claim(&claims,row,10),selected_claim(&claims,row,11),selected_claim(&claims,row,12),selected_claim(&claims,row,13),selected_claim(&claims,row,14),selected_claim(&claims,row,15)]
}

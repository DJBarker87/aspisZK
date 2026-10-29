//! Allocation-bounded SBF-safe Copy lane for the eight-lane Pool V1
//! pair-forest relation.
//!
//! Runtime evaluation consumes only generated patterns, endpoints and fixed
//! active-row masks. The allocation-heavy typed registry remains the
//! independent host compiler/reference boundary and is not linked on SBF.


// Closure-free array construction, evaluated in increasing source index order.
macro_rules! qm31_array {
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

#[cfg(any(test, feature = "optimized-terminal"))]
use crate::host_terminal_field::{qm31_sum_products2, qm31_sum_products3, qm31_sum_products4};
use crate::host_terminal_field::PreparedQm31Multiplier;
use aspis_core::field::{CM31, M31, QM31};

use aspis_statement::poseidon2::POSEIDON2_WIDTH;

pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1: usize = 1024;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1: usize = 16;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1: usize = 136;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1: usize = 14;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
    if cfg!(feature = "optimized-terminal") {
        2
    } else {
        1
    };
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
    core::mem::size_of::<Selectors>();
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1: usize =
    if cfg!(feature = "optimized-terminal") {
        103 * core::mem::size_of::<QM31>()
    } else {
        0
    };
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_BYTES_V1: usize =
    POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1
        + POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1;
pub const PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1: u64 =
    constants::ACTIVE_ROWS_FINGERPRINT;

/// Exact SBF-safe active-row schedule consumed by the selected verifier.
/// Host generation tests independently replay it from the typed tuple registry.
pub fn pool_v1_pair_forest_copy_active_row_masks_compiled_v1() -> &'static [u16; 64] {
    &constants::ACTIVE_ROW_MASKS
}

/// Frozen row-to-group schedule generated from the exact pair-forest copy
/// registry.  The selected verifier consumes this directly instead of
/// rebuilding and deduplicating public layout data on every transaction.
pub fn pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1() -> &'static [u8; 64] {
    &constants::INACTIVE_ROW_GROUPS
}

/// Deduplicated inactive masks referenced by
/// [`pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1`].
pub fn pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1() -> &'static [u16] {
    &constants::INACTIVE_GROUP_MASKS
}

const _: () = assert!(POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1);
const _: () = assert!(constants::COPY_LINKS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1);
const _: () =
    assert!(constants::COPY_PATTERNS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1);
const _: () = assert!(constants::ACTIVE_ROW_MASKS.len() == 64);
const _: () = assert!(constants::INACTIVE_ROW_GROUPS.len() == 64);
const _: () = assert!(constants::INACTIVE_GROUP_MASKS.len() <= 64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestCompiledVariantV1 {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestCompiledCopyTerminalV1 {
    pub residual: QM31,
    pub active: QM31,
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PairForestPattern {
    /// 0 = zero, 1 = row-local C1 cell plus a canonical M31 offset.
    kinds: [u8; POSEIDON2_WIDTH],
    columns: [u8; POSEIDON2_WIDTH],
    offsets: [u32; POSEIDON2_WIDTH],
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PairForestEndpoint {
    row: u16,
    slot: u8,
    pattern: u8,
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PairForestLink {
    tag: u32,
    /// 0 = one, 1 = transfer, 2 = withdrawal, 3 = append-left,
    /// 4 = append-right.
    weight_kind: u8,
    weight_level: u8,
    producer: CompiledPoolV1PairForestEndpoint,
    consumer: CompiledPoolV1PairForestEndpoint,
}

mod constants {
    use super::{
        CompiledPoolV1PairForestEndpoint, CompiledPoolV1PairForestLink,
        CompiledPoolV1PairForestPattern,
    };
    include!("host_copy_terminal_constants.rs");
}

#[inline(always)]
fn lift_m31(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn selector_mask_sum_16(values:[QM31;16],mask:u16)->QM31 {
    match mask {
        1749 => QM31::ZERO.add(values[0]).add(values[2]).add(values[4]).add(values[6]).add(values[7]).add(values[9]).add(values[10]),
        2048 => QM31::ZERO.add(values[11]),
        2049 => QM31::ZERO.add(values[0]).add(values[11]),
        4097 => QM31::ZERO.add(values[0]).add(values[12]),
        6144 => QM31::ZERO.add(values[11]).add(values[12]),
        6145 => QM31::ZERO.add(values[0]).add(values[11]).add(values[12]),
        26214 => QM31::ZERO.add(values[1]).add(values[2]).add(values[5]).add(values[6]).add(values[9]).add(values[10]).add(values[13]).add(values[14]),
        _ => panic!("outside frozen active mask set"),
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Selectors {
    pub(crate) high: [QM31; 64],
    pub(crate) low: [QM31; 16],
}

impl Selectors {
    fn expand<const N: usize>(point: &[QM31; 10], start: usize, count: usize) -> [QM31; N] {
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
        Self { high: Self::expand(point, 0, 6), low: Self::expand(point, 6, 4) }
    }

    #[inline(never)]
    pub(crate) fn boxed_at_point(point: &[QM31;10])->Self {Self::at_point(point)}

    #[inline(always)]
    pub(crate) fn row(&self, row: usize) -> QM31 {
        debug_assert!(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1);
        self.high[row >> 4].mul(self.low[row & 15])
    }

    #[cfg(any(test, not(feature = "optimized-terminal")))]
    fn active_literal(&self) -> QM31 {
        let mut sum = QM31::ZERO;
        let mut block = 0usize;
        while block < 64 {
            sum=active_block227(*self,block,sum);
            block += 1;
        }
        sum
    }

    #[cfg(any(test, feature = "optimized-terminal"))]
    fn active_mask_basis(&self) -> QM31 {
        // Candidate specialization of the seven frozen active masks. Their
        // set-bit counts are all at most eight, so selector_mask_sum_16 takes
        // its non-complement branch and visits these low indices in order.
        const MASKS: [u16; 7] = [6144, 6145, 4097, 2048, 2049, 26214, 1749];
        let mut high_sums = [QM31::ZERO; MASKS.len()];
        let mut block = 0usize;
        while block < constants::ACTIVE_ROW_MASKS.len() {
            let mask = constants::ACTIVE_ROW_MASKS[block];
            let coordinate = match mask {
                6144 => 0,
                6145 => 1,
                4097 => 2,
                2048 => 3,
                2049 => 4,
                26214 => 5,
                1749 => 6,
                _ => unreachable!("generated Copy active mask outside frozen basis"),
            };
            high_sums[coordinate] = high_sums[coordinate].add(self.high[block]);
            block += 1;
        }
        let mut sum = QM31::ZERO;
        let mut coordinate = 0usize;
        while coordinate < MASKS.len() {
            let low_sum = match coordinate {
                0 => self.low[11].add(self.low[12]),
                1 => self.low[0].add(self.low[11]).add(self.low[12]),
                2 => self.low[0].add(self.low[12]),
                3 => self.low[11],
                4 => self.low[0].add(self.low[11]),
                5 => self.low[1].add(self.low[2]).add(self.low[5]).add(self.low[6])
                    .add(self.low[9]).add(self.low[10]).add(self.low[13]).add(self.low[14]),
                6 => self.low[0].add(self.low[2]).add(self.low[4]).add(self.low[6])
                    .add(self.low[7]).add(self.low[9]).add(self.low[10]),
                _ => unreachable!("coordinate outside frozen active-mask basis"),
            };
            sum = sum.add(high_sums[coordinate].mul(low_sum));
            coordinate += 1;
        }
        sum
    }

    #[inline(always)]
    fn active(&self) -> QM31 {
        #[cfg(not(feature = "optimized-terminal"))]
        return self.active_literal();
        #[cfg(feature = "optimized-terminal")]
        return self.active_mask_basis();
    }
}

#[cfg(any(test, not(feature = "optimized-terminal")))]
fn pattern_values_literal(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
    let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut power = lambda;
    let mut limb = 0usize;
    while limb < POSEIDON2_WIDTH {
        powers[limb] = power;
        power = power.mul(lambda);
        limb += 1;
    }
    let mut result = [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
    let mut pattern_index = 0usize;
    while pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 {
        let pattern = constants::COPY_PATTERNS[pattern_index];
        let mut value = QM31::ZERO;
        limb = 0;
        while limb < POSEIDON2_WIDTH {
            value = pattern_limb227(pattern,limb,*openings,powers,value);
            limb += 1;
        }
        result[pattern_index] = value;
        pattern_index += 1;
    }
    result
}

/// Exact CSE for the frozen fourteen-pattern table. Pattern 0 is the two
/// adjacent eight-limb windows, patterns 2 and 3 are exact six-limb prefixes,
/// and pattern 10 differs from pattern 13 only by its final public offset.
#[cfg(any(test, feature = "optimized-terminal"))]
fn pattern_values_windowed(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
    let mut powers = [QM31::ZERO; 8];
    let mut power = lambda;
    let mut slot = 0usize;
    while slot < powers.len() {
        powers[slot] = power;
        power = power.mul(lambda);
        slot += 1;
    }
    let prepared = [
        PreparedQm31Multiplier::new(powers[0]),
        PreparedQm31Multiplier::new(powers[1]),
        PreparedQm31Multiplier::new(powers[2]),
        PreparedQm31Multiplier::new(powers[3]),
        PreparedQm31Multiplier::new(powers[4]),
        PreparedQm31Multiplier::new(powers[5]),
        PreparedQm31Multiplier::new(powers[6]),
        PreparedQm31Multiplier::new(powers[7]),
    ];
    let window_0 = pattern_window(openings, prepared, 0);
    let window_1 = pattern_window(openings, prepared, 1);
    let window_2 = pattern_window(openings, prepared, 2);
    let window_8 = pattern_window(openings, prepared, 8);
    let mut result = [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
    result[0] = window_0.add(prepared[7].mul(window_8));
    result[1] = window_0;
    result[2] = window_2
        .sub(prepared[6].mul(openings[8]))
        .sub(prepared[7].mul(openings[9]));
    result[3] = window_0
        .sub(prepared[6].mul(openings[6]))
        .sub(prepared[7].mul(openings[7]));
    result[4] = prepared[0]
        .mul(openings[0])
        .add(prepared[1].mul(openings[1]));
    result[5] = prepared[0]
        .mul(openings[6])
        .add(prepared[1].mul(openings[7]));
    result[6] = prepared[0].mul(openings[0]);
    result[7] = prepared[0].mul(openings[10]);
    result[8] = prepared[0].mul(openings[1]);
    result[9] = prepared[0].mul(openings[2]);
    result[10] = window_8.add(prepared[7].mul(lift_m31(M31(1_051_521_018))));
    result[11] = window_2;
    result[12] = window_1;
    result[13] = window_8;
    result
}

fn pattern_values(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
    #[cfg(not(feature = "optimized-terminal"))]
    return pattern_values_literal(openings, lambda);
    #[cfg(feature = "optimized-terminal")]
    return pattern_values_windowed(openings, lambda);
}

#[derive(Clone, Copy)]
struct CopyRowExtension {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
    let denominators = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];
    let producer_denominator = denominators[0].mul(denominators[1]);
    let consumer_denominator = denominators[2].mul(denominators[3]);
    let producer_numerator = row.producer_weights[0]
        .mul(denominators[1])
        .add(row.producer_weights[1].mul(denominators[0]));
    let consumer_numerator = row.consumer_weights[0]
        .mul(denominators[3])
        .add(row.consumer_weights[1].mul(denominators[2]));
    producer_denominator
        .mul(helper.mul(consumer_denominator).add(consumer_numerator))
        .sub(consumer_denominator.mul(producer_numerator))
}

#[inline(always)]
fn link_weight(
    link: CompiledPoolV1PairForestLink,
    append_index: u64,
    variant: PoolV1PairForestCompiledVariantV1,
) -> M31 {
    match link.weight_kind {
        0 => M31::ONE,
        1 => M31(u32::from(
            variant == PoolV1PairForestCompiledVariantV1::PrivateTransfer,
        )),
        2 => M31(u32::from(
            variant == PoolV1PairForestCompiledVariantV1::Withdrawal,
        )),
        3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),
        4 => M31(((append_index >> link.weight_level) & 1) as u32),
        _ => unreachable!("generated Pool V1 pair-forest Copy weight"),
    }
}

/// Exact specialization of `sum + selector * weight` for the generated Copy
/// grammar. `link_weight` has image `{0,1}` for every variant and append
/// index; focused tests bind that image to every checked-in generated link.
#[cfg(any(test, feature = "optimized-terminal"))]
#[inline(always)]
fn add_binary_weight(sum: QM31, selector: QM31, weight: M31) -> QM31 {
    match weight.0 {
        0 => sum,
        1 => sum.add(selector),
        _ => unreachable!("generated Pool V1 pair-forest Copy weight is not binary"),
    }
}

/// Small direct-mapped memo for the checked-in generated endpoint stream.
/// The row tag makes collision behavior purely a performance concern: a
/// collision always recomputes the literal selector before replacing a slot.
#[cfg(any(test, feature = "optimized-terminal"))]
struct EndpointSelectorCache {
    rows: [u16; 32],
    values: [QM31; 32],
}

#[cfg(any(test, feature = "optimized-terminal"))]
impl EndpointSelectorCache {
    fn new() -> Self {
        Self {
            rows: [u16::MAX; 32],
            values: [QM31::ZERO; 32],
        }
    }

    #[inline(always)]
    fn selector(&mut self, row: u16, selectors: &Selectors) -> QM31 {
        let slot = usize::from(row) & (self.rows.len() - 1);
        if self.rows[slot] == row {
            self.values[slot]
        } else {
            let value = selectors.row(usize::from(row));
            self.rows[slot] = row;
            self.values[slot] = value;
            value
        }
    }
}

fn accumulate_endpoint(
    values: &mut [QM31; 2],
    weights: &mut [QM31; 2],
    endpoint: CompiledPoolV1PairForestEndpoint,
    tag: u32,
    weight: M31,
    patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
    selectors: &Selectors,
    #[cfg(feature = "optimized-terminal")]
    selector_cache: &mut EndpointSelectorCache,
) {
    #[cfg(not(feature = "optimized-terminal"))]
    let selector = selectors.row(usize::from(endpoint.row));
    #[cfg(feature = "optimized-terminal")]
    let selector = selector_cache.selector(endpoint.row, selectors);
    let slot = usize::from(endpoint.slot);
    #[cfg(not(feature = "optimized-terminal"))]
    {
        weights[slot] = weights[slot].add(selector.mul_m31(weight));
    }
    #[cfg(feature = "optimized-terminal")]
    {
        weights[slot] = add_binary_weight(weights[slot], selector, weight);
    }
    let compressed = lift_m31(M31(tag)).add(patterns[usize::from(endpoint.pattern)]);
    values[slot] = values[slot].add(selector.mul(compressed));
}

/// Exact support of the four `(side, slot)` linear forms in the generated
/// fourteen-pattern basis.  The masks are derived from `COPY_LINKS` and are
/// checked against that table in the focused tests below.
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_GROUP_SUPPORT: [u16; 4] = [0x0ed7, 0x2042, 0x1dcb, 0x01e2];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_COORDINATES: [[u8; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1]; 4] = [
    [
        0,
        1,
        2,
        u8::MAX,
        3,
        u8::MAX,
        4,
        5,
        u8::MAX,
        6,
        7,
        8,
        u8::MAX,
        u8::MAX,
    ],
    [
        u8::MAX,
        9,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        10,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        11,
    ],
    [
        12,
        13,
        u8::MAX,
        14,
        u8::MAX,
        u8::MAX,
        15,
        16,
        17,
        u8::MAX,
        18,
        19,
        20,
        u8::MAX,
    ],
    [
        u8::MAX,
        21,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        22,
        23,
        24,
        25,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
    ],
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_COORDINATE_PATTERNS: [u8; 26] = [
    0, 1, 2, 4, 6, 7, 9, 10, 11, 1, 6, 13, 0, 1, 3, 6, 7, 8, 10, 11, 12, 1, 5, 6, 7, 8,
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_GROUP_OFFSETS: [usize; 5] = [0, 9, 12, 21, 26];

#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_GROUP_LOCAL_COORDINATE_GROUPS: [u8; 30] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3,
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_GROUP_LOCAL_COORDINATE_LOCALS: [u8; 30] = [
    0, 1, 2, 4, 6, 10, 11, 12, 14, 2, 6, 10, 11, 12, 14, 0, 1, 2, 4, 5, 6, 7, 9, 10, 12, 13, 6, 7,
    9, 12,
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_GROUP_LOCAL_GROUP_OFFSETS: [usize; 5] = [0, 9, 15, 26, 30];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_LOCAL_COORDINATE_GROUPS: [u8; 43] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3,
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_LOCAL_COORDINATE_PATTERNS: [u8; 43] = [
    0, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6, 7, 7, 7, 9, 10, 11, 1, 6, 13, 13, 13, 13, 0, 1, 3, 6, 7, 7, 7,
    8, 10, 11, 11, 12, 12, 12, 12, 1, 5, 6, 7, 8,
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_LOCAL_COORDINATE_LOCALS: [u8; 43] = [
    11, 2, 6, 10, 11, 12, 14, 12, 12, 1, 12, 0, 2, 4, 6, 0, 10, 11, 12, 2, 6, 10, 14, 0, 12, 12, 6,
    0, 2, 4, 7, 0, 9, 10, 1, 5, 9, 13, 12, 12, 7, 9, 6,
];
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_LOCAL_OUTPUT_COORDINATES: [u8; 43] = [
    0, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5, 5, 5, 6, 7, 8, 9, 10, 11, 11, 11, 11, 12, 13, 14, 15, 16,
    16, 16, 17, 18, 19, 19, 20, 20, 20, 20, 21, 22, 23, 24, 25,
];

#[cfg(any(test, feature = "optimized-terminal"))]
const fn build_group_local_coordinates() -> [[u8; 16]; 4] {
    let mut output = [[u8::MAX; 16]; 4];
    let mut coordinate = 0usize;
    while coordinate < COPY_GROUP_LOCAL_COORDINATE_GROUPS.len() {
        output[COPY_GROUP_LOCAL_COORDINATE_GROUPS[coordinate] as usize]
            [COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate] as usize] = coordinate as u8;
        coordinate += 1;
    }
    output
}

#[cfg(any(test, feature = "optimized-terminal"))]
const fn build_pattern_local_coordinates() -> [[[u8; 16]; 14]; 4] {
    let mut output = [[[u8::MAX; 16]; 14]; 4];
    let mut coordinate = 0usize;
    while coordinate < COPY_PATTERN_LOCAL_COORDINATE_GROUPS.len() {
        output[COPY_PATTERN_LOCAL_COORDINATE_GROUPS[coordinate] as usize]
            [COPY_PATTERN_LOCAL_COORDINATE_PATTERNS[coordinate] as usize]
            [COPY_PATTERN_LOCAL_COORDINATE_LOCALS[coordinate] as usize] = coordinate as u8;
        coordinate += 1;
    }
    output
}

#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_GROUP_LOCAL_COORDINATES: [[u8; 16]; 4] = build_group_local_coordinates();
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_PATTERN_LOCAL_COORDINATES: [[[u8; 16]; 14]; 4] = build_pattern_local_coordinates();
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_SELECTOR_TENSOR_TAG_OFFSET: usize = 0;
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_SELECTOR_TENSOR_WEIGHT_OFFSET: usize = 30;
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_SELECTOR_TENSOR_PATTERN_OFFSET: usize = 60;
#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_SELECTOR_TENSOR_SCRATCH: usize = 103;

#[cfg(any(test, feature = "optimized-terminal"))]
const fn build_copy_tag_coordinate_offsets() -> [u16; 31] {
    let mut counts = [0u16; 30];
    let mut link_index = 0usize;
    while link_index < constants::COPY_LINKS.len() {
        let link = constants::COPY_LINKS[link_index];
        let producer_group = link.producer.slot as usize;
        let producer_local = link.producer.row as usize & 15;
        let producer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[producer_group][producer_local] as usize;
        counts[producer_coordinate] += 1;

        let consumer_group = 2 + link.consumer.slot as usize;
        let consumer_local = link.consumer.row as usize & 15;
        let consumer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[consumer_group][consumer_local] as usize;
        counts[consumer_coordinate] += 1;
        link_index += 1;
    }
    let mut offsets = [0u16; 31];
    let mut coordinate = 0usize;
    while coordinate < counts.len() {
        offsets[coordinate + 1] = offsets[coordinate] + counts[coordinate];
        coordinate += 1;
    }
    offsets
}

#[cfg(any(test, feature = "optimized-terminal"))]
const COPY_TAG_COORDINATE_OFFSETS: [u16; 31] = build_copy_tag_coordinate_offsets();

#[cfg(any(test, feature = "optimized-terminal"))]
const fn build_copy_tag_terms() -> ([u8; 272], [u32; 272]) {
    let mut blocks = [0u8; 272];
    let mut tags = [0u32; 272];
    let mut cursors = [0u16; 30];
    let mut coordinate = 0usize;
    while coordinate < cursors.len() {
        cursors[coordinate] = COPY_TAG_COORDINATE_OFFSETS[coordinate];
        coordinate += 1;
    }

    let mut link_index = 0usize;
    while link_index < constants::COPY_LINKS.len() {
        let link = constants::COPY_LINKS[link_index];

        let producer_group = link.producer.slot as usize;
        let producer_row = link.producer.row as usize;
        let producer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[producer_group][producer_row & 15] as usize;
        let producer_output = cursors[producer_coordinate] as usize;
        blocks[producer_output] = (producer_row >> 4) as u8;
        tags[producer_output] = link.tag;
        cursors[producer_coordinate] += 1;

        let consumer_group = 2 + link.consumer.slot as usize;
        let consumer_row = link.consumer.row as usize;
        let consumer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[consumer_group][consumer_row & 15] as usize;
        let consumer_output = cursors[consumer_coordinate] as usize;
        blocks[consumer_output] = (consumer_row >> 4) as u8;
        tags[consumer_output] = link.tag;
        cursors[consumer_coordinate] += 1;

        link_index += 1;
    }
    (blocks, tags)
}

#[cfg(any(test, feature = "optimized-terminal"))]
static COPY_TAG_TERMS: ([u8; 272], [u32; 272]) = build_copy_tag_terms();

/// Evaluate one frozen Copy-tag coordinate with four-product lazy M31
/// reduction. Each raw channel is strictly below
/// `4 * (P - 1)^2 < 2^64` before reduction.
#[cfg(any(test, feature = "optimized-terminal"))]
#[inline(never)]
fn copy_tag_coordinate_dot(coordinate: usize, selectors: &Selectors) -> QM31 {
    let mut output = [M31::ZERO; 4];
    let mut index = usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);
    let end = usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate + 1]);
    while index < end {
        let chunk_end = core::cmp::min(index + 4, end);
        let mut raw = [0u64; 4];
        while index < chunk_end {
            let value = selectors.high[usize::from(COPY_TAG_TERMS.0[index])];
            let tag = u64::from(COPY_TAG_TERMS.1[index]);
            raw[0] += u64::from(value.c0.a.0) * tag;
            raw[1] += u64::from(value.c0.b.0) * tag;
            raw[2] += u64::from(value.c1.a.0) * tag;
            raw[3] += u64::from(value.c1.b.0) * tag;
            index += 1;
        }
        let mut limb = 0usize;
        while limb < output.len() {
            output[limb] = output[limb].add(M31::reduce_u64(raw[limb]));
            limb += 1;
        }
    }
    QM31 {
        c0: CM31::new(output[0], output[1]),
        c1: CM31::new(output[2], output[3]),
    }
}

#[cfg(any(test, feature = "optimized-terminal"))]
#[inline(always)]
fn qm31_sum_products_up_to4(left: [QM31; 4], right: [QM31; 4], count: usize) -> QM31 {
    match count {
        1 => left[0].mul(right[0]),
        2 => qm31_sum_products2([left[0], left[1]], [right[0], right[1]]),
        3 => qm31_sum_products3([left[0], left[1], left[2]], [right[0], right[1], right[2]]),
        4 => qm31_sum_products4(left, right),
        _ => unreachable!("Copy finish dot batch width"),
    }
}

#[cfg(all(
    any(test, feature = "optimized-terminal"),
    not(feature = "optimized-terminal")
))]
#[inline(always)]
fn copy_tag_coordinate_value(scratch: &[QM31], coordinate: usize, _selectors: &Selectors) -> QM31 {
    scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + coordinate]
}

#[cfg(feature = "optimized-terminal")]
#[inline(always)]
fn copy_tag_coordinate_value(_scratch: &[QM31], coordinate: usize, selectors: &Selectors) -> QM31 {
    copy_tag_coordinate_dot(coordinate, selectors)
}

/// Accumulate one compiled endpoint after changing from the endpoint basis to
/// the fixed tuple-pattern basis:
///
/// `s * (tag + pattern[p]) = s * tag + pattern[p] * s`.
///
/// The first product is by an M31 value.  Dynamic QM31 pattern values are
/// multiplied only once per nonzero `(side, slot, pattern)` coordinate after
/// all 272 endpoint selectors have been collected.
#[cfg(any(test, feature = "optimized-terminal"))]
fn accumulate_endpoint_pattern_basis(
    tag_values: &mut [QM31; 4],
    pattern_selectors: &mut [QM31; 26],
    weights: &mut [QM31; 2],
    side: usize,
    endpoint: CompiledPoolV1PairForestEndpoint,
    tag: u32,
    weight: M31,
    selectors: &Selectors,
    #[cfg(feature = "optimized-terminal")]
    selector_cache: &mut EndpointSelectorCache,
) {
    #[cfg(not(feature = "optimized-terminal"))]
    let selector = selectors.row(usize::from(endpoint.row));
    #[cfg(feature = "optimized-terminal")]
    let selector = selector_cache.selector(endpoint.row, selectors);
    let slot = usize::from(endpoint.slot);
    let group = side + slot;
    tag_values[group] = tag_values[group].add(selector.mul_m31(M31(tag)));
    let pattern = usize::from(endpoint.pattern);
    let coordinate = COPY_PATTERN_COORDINATES[group][pattern];
    debug_assert_ne!(coordinate, u8::MAX);
    let coordinate = usize::from(coordinate);
    pattern_selectors[coordinate] = pattern_selectors[coordinate].add(selector);
    #[cfg(not(feature = "optimized-terminal"))]
    {
        weights[slot] = weights[slot].add(selector.mul_m31(weight));
    }
    #[cfg(feature = "optimized-terminal")]
    {
        weights[slot] = add_binary_weight(weights[slot], selector, weight);
    }
}

#[cfg(any(test, feature = "optimized-terminal"))]
fn finish_pattern_basis_values(
    mut values: [QM31; 4],
    pattern_selectors: [QM31; 26],
    patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
) -> [QM31; 4] {
    let mut group = 0usize;
    while group < values.len() {
        let mut coordinate = COPY_PATTERN_GROUP_OFFSETS[group];
        while coordinate < COPY_PATTERN_GROUP_OFFSETS[group + 1] {
            let pattern = usize::from(COPY_PATTERN_COORDINATE_PATTERNS[coordinate]);
            values[group] = values[group].add(patterns[pattern].mul(pattern_selectors[coordinate]));
            coordinate += 1;
        }
        group += 1;
    }
    values
}

#[cfg(any(test, feature = "optimized-terminal"))]
#[inline(never)]
fn selected_binary_weight(high: QM31, weight: M31) -> QM31 {
    if weight.0 == 1 {
        high
    } else {
        QM31::ZERO
    }
}

#[cfg(any(test, feature = "optimized-terminal"))]
fn accumulate_endpoint_selector_tensor_basis(
    scratch: &mut [QM31],
    side: usize,
    endpoint: CompiledPoolV1PairForestEndpoint,
    tag: u32,
    weight: M31,
    selectors: &Selectors,
) {
    let group = side + usize::from(endpoint.slot);
    let row = usize::from(endpoint.row);
    let local = row & 15;
    let high = selectors.high[row >> 4];
    let group_local = usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);
    #[cfg(not(feature = "optimized-terminal"))]
    {
        scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + group_local] =
            scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + group_local].add(high.mul_m31(M31(tag)));
    }
    #[cfg(feature = "optimized-terminal")]
    let _ = tag;
    let weight_index = COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + group_local;
    scratch[weight_index] =
        scratch[weight_index].add(selected_binary_weight(high, weight));
    let pattern_local =
        usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]);
    scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local] =
        scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local].add(high);
}

#[cfg(any(test, feature = "optimized-terminal"))]
fn finish_selector_tensor_basis(
    scratch: &[QM31],
    patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
    selectors: &Selectors,
) -> ([QM31; 4], [QM31; 4]) {
    let mut values = [QM31::ZERO; 4];
    let mut weights = [QM31::ZERO; 4];
    #[cfg(not(feature = "optimized-terminal"))]
    {
        let mut coordinate = 0usize;
        while coordinate < COPY_GROUP_LOCAL_COORDINATE_GROUPS.len() {
            let group = usize::from(COPY_GROUP_LOCAL_COORDINATE_GROUPS[coordinate]);
            let low = selectors.low[usize::from(COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate])];
            let tag_value = copy_tag_coordinate_value(scratch, coordinate, selectors);
            values[group] = values[group].add(tag_value.mul(low));
            weights[group] = weights[group]
                .add(scratch[COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + coordinate].mul(low));
            coordinate += 1;
        }
    }
    #[cfg(feature = "optimized-terminal")]
    {
        let mut group = 0usize;
        while group < values.len() {
            let end = COPY_GROUP_LOCAL_GROUP_OFFSETS[group + 1];
            let mut coordinate = COPY_GROUP_LOCAL_GROUP_OFFSETS[group];
            while coordinate < end {
                let count = core::cmp::min(4, end - coordinate);
                let tag_values: [QM31; 4] = qm31_array!(4, index, {
                    if index < count {
                        copy_tag_coordinate_value(scratch, coordinate + index, selectors)
                    } else {
                        QM31::ZERO
                    }
                });
                let weight_values: [QM31; 4] = qm31_array!(4, index, {
                    if index < count {
                        scratch[COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + coordinate + index]
                    } else {
                        QM31::ZERO
                    }
                });
                let lows: [QM31; 4] = qm31_array!(4, index, {
                    if index < count {
                        selectors.low
                            [usize::from(COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate + index])]
                    } else {
                        QM31::ZERO
                    }
                });
                values[group] =
                    values[group].add(qm31_sum_products_up_to4(tag_values, lows, count));
                weights[group] =
                    weights[group].add(qm31_sum_products_up_to4(weight_values, lows, count));
                coordinate += count;
            }
            group += 1;
        }
    }
    let mut pattern_selectors = [QM31::ZERO; 26];
    let mut coordinate = 0;
    while coordinate < COPY_PATTERN_LOCAL_COORDINATE_GROUPS.len() {
        let output = usize::from(COPY_PATTERN_LOCAL_OUTPUT_COORDINATES[coordinate]);
        let low = selectors.low[usize::from(COPY_PATTERN_LOCAL_COORDINATE_LOCALS[coordinate])];
        pattern_selectors[output] = pattern_selectors[output]
            .add(scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + coordinate].mul(low));
        coordinate += 1;
    }
    (
        finish_pattern_basis_values(values, pattern_selectors, patterns),
        weights,
    )
}

pub(crate) fn evaluate_with_selectors(
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    selectors: &Selectors,
    lambda: QM31,
    chi: QM31,
    append_index: u64,
    variant: PoolV1PairForestCompiledVariantV1,
) -> PoolV1PairForestCompiledCopyTerminalV1 {
    let patterns = pattern_values(openings, lambda);
    let mut row = CopyRowExtension {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [QM31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [QM31::ZERO; 2],
    };
    #[cfg(all(
        feature = "optimized-terminal",
        not(feature = "optimized-terminal")
    ))]
    let mut selector_cache = EndpointSelectorCache::new();
    #[cfg(all(
        feature = "optimized-terminal",
        not(feature = "optimized-terminal")
    ))]
    let mut tag_values = [QM31::ZERO; 4];
    #[cfg(all(
        feature = "optimized-terminal",
        not(feature = "optimized-terminal")
    ))]
    let mut pattern_selectors = [QM31::ZERO; 26];
    #[cfg(feature = "optimized-terminal")]
    let mut selector_tensor_scratch = [QM31::ZERO; COPY_SELECTOR_TENSOR_SCRATCH];
    let mut link_index = 0usize;
    while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
        let link = constants::COPY_LINKS[link_index];
        let weight = link_weight(link, append_index, variant);
        #[cfg(all(
            not(feature = "optimized-terminal"),
            not(feature = "optimized-terminal")
        ))]
        #[cfg(not(feature = "optimized-terminal"))]
        {
            accumulate_endpoint(
                &mut row.producer_values,
                &mut row.producer_weights,
                link.producer,
                link.tag,
                weight,
                &patterns,
                selectors,
            );
            accumulate_endpoint(
                &mut row.consumer_values,
                &mut row.consumer_weights,
                link.consumer,
                link.tag,
                weight,
                &patterns,
                selectors,
            );
        }
        #[cfg(all(
            not(feature = "optimized-terminal"),
            not(feature = "optimized-terminal")
        ))]
        #[cfg(feature = "optimized-terminal")]
        {
            accumulate_endpoint(
                &mut row.producer_values,
                &mut row.producer_weights,
                link.producer,
                link.tag,
                weight,
                &patterns,
                selectors,
                &mut selector_cache,
            );
            accumulate_endpoint(
                &mut row.consumer_values,
                &mut row.consumer_weights,
                link.consumer,
                link.tag,
                weight,
                &patterns,
                selectors,
                &mut selector_cache,
            );
        }
        #[cfg(all(
            feature = "optimized-terminal",
            not(feature = "optimized-terminal")
        ))]
        {
            accumulate_endpoint_pattern_basis(
                &mut tag_values,
                &mut pattern_selectors,
                &mut row.producer_weights,
                0,
                link.producer,
                link.tag,
                weight,
                selectors,
                #[cfg(feature = "optimized-terminal")]
                &mut selector_cache,
            );
            accumulate_endpoint_pattern_basis(
                &mut tag_values,
                &mut pattern_selectors,
                &mut row.consumer_weights,
                2,
                link.consumer,
                link.tag,
                weight,
                selectors,
                #[cfg(feature = "optimized-terminal")]
                &mut selector_cache,
            );
        }
        #[cfg(feature = "optimized-terminal")]
        {
            accumulate_endpoint_selector_tensor_basis(
                &mut selector_tensor_scratch,
                0,
                link.producer,
                link.tag,
                weight,
                selectors,
            );
            accumulate_endpoint_selector_tensor_basis(
                &mut selector_tensor_scratch,
                2,
                link.consumer,
                link.tag,
                weight,
                selectors,
            );
        }
        link_index += 1;
    }
    #[cfg(all(
        feature = "optimized-terminal",
        not(feature = "optimized-terminal")
    ))]
    {
        let values = finish_pattern_basis_values(tag_values, pattern_selectors, &patterns);
        row.producer_values = [values[0], values[1]];
        row.consumer_values = [values[2], values[3]];
    }
    #[cfg(feature = "optimized-terminal")]
    {
        let (values, weights) =
            finish_selector_tensor_basis(&selector_tensor_scratch, &patterns, selectors);
        row.producer_values = [values[0], values[1]];
        row.consumer_values = [values[2], values[3]];
        row.producer_weights = [weights[0], weights[1]];
        row.consumer_weights = [weights[2], weights[3]];
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
pub fn evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    append_index: u64,
    variant: PoolV1PairForestCompiledVariantV1,
) -> PoolV1PairForestCompiledCopyTerminalV1 {
    let selectors = Selectors::boxed_at_point(point);
    evaluate_with_selectors(
        openings,
        h1_z,
        &selectors,
        lambda,
        chi,
        append_index,
        variant,
    )
}

pub fn pool_v1_pair_forest_copy_active_at_point_compiled_v1(point: &[QM31; 10]) -> QM31 {
    Selectors::at_point(point).active()
}

/// Source-extraction wrapper for a Boolean terminal row. `variant` is zero
/// for private transfer and one for withdrawal.
#[doc(hidden)]
pub fn pool_v1_pair_forest_copy_lane_boolean_extraction_v1(
    variant: u8,
    selected_row: u16,
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    lambda: QM31,
    chi: QM31,
    append_index: u64,
) -> Option<PoolV1PairForestCompiledCopyTerminalV1> {
    if usize::from(selected_row) >= POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1 {
        return None;
    }
    let variant = match variant {
        0 => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
        1 => PoolV1PairForestCompiledVariantV1::Withdrawal,
        _ => return None,
    };
    let mut high = [QM31::ZERO; 64];
    let mut low = [QM31::ZERO; 16];
    high[usize::from(selected_row >> 4)] = QM31::ONE;
    low[usize::from(selected_row & 15)] = QM31::ONE;
    let selectors = Selectors { high, low };
    Some(evaluate_with_selectors(
        openings,
        h1_z,
        &selectors,
        lambda,
        chi,
        append_index,
        variant,
    ))
}

#[inline(always)]
fn pattern_window(openings: &[QM31; POSEIDON2_WIDTH], prepared: [PreparedQm31Multiplier; 8], start: usize) -> QM31 {
    let mut value = QM31::ZERO;
    let mut slot = 0usize;
    while slot < 8 {
        value = value.add(prepared[slot].mul(openings[start + slot]));
        slot += 1;
    }
    value
}

fn pattern_limb227(pattern:CompiledPoolV1PairForestPattern,limb:usize,openings:[QM31;16],powers:[QM31;16],value:QM31)->QM31 {
    if pattern.kinds[limb]==1 {
        let source=openings[usize::from(pattern.columns[limb])].add(lift_m31(M31(pattern.offsets[limb])));
        value.add(powers[limb].mul(source))
    } else {value}
}

fn active_block227(selectors:Selectors,block:usize,sum:QM31)->QM31 {
    let mask=constants::ACTIVE_ROW_MASKS[block];
    if mask!=0 { sum.add(selectors.high[block].mul(selector_mask_sum_16(selectors.low,mask))) } else {sum}
}

fn mask_step227(values:[QM31;16],index:usize,sum:QM31,complement:bool)->QM31 {
    if complement {sum.sub(values[index])} else {sum.add(values[index])}
}

// Harness-only adapters after an unmodified module prefix.
pub(crate) mod access16 { use super::*;
pub fn mask(v:&[QM31;16],m:u16)->QM31 { selector_mask_sum_16(*v,m) }
#[cfg(not(feature="optimized-terminal"))]
pub fn active(h:[QM31;64],l:[QM31;16])->QM31 { Selectors{high:h,low:l}.active_literal() }
pub fn pattern(v:&[QM31;16],l:QM31)->[QM31;14] { pattern_values_literal(v,l) }
pub fn masks()->[u16;64] { constants::ACTIVE_ROW_MASKS }
}

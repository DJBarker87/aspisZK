//! Host-only state-only masking helper and complete public-view inventory.
//!
//! This remains production-neutral: it does not choose the PCS envelope or
//! mutate Solana accounts. It does freeze mask seed derivation, one-time nonce
//! handling, the exact affine mask oracle, and the byte inventory which a
//! complete HVZK argument must cover.

use std::collections::BTreeSet;

use aspis_core::field::{CM31, M31, P, QM31};
#[cfg(test)]
use aspis_core::state_only_hiding::{
    begin_state_only_hiding_precommit, STATE_ONLY_H1_PADDING_MASK_FREE_QM31,
};
use aspis_core::state_only_hiding::{
    begin_state_only_masked_sumcheck, state_only_selected_mask_value, StateOnlyHidingContext,
    StateOnlyHidingScheduleError, PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
    PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
    PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
    PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT, STATE_ONLY_H1_PADDING_MASK_END,
    STATE_ONLY_H1_PADDING_MASK_START, STATE_ONLY_HIDING_C1_COLUMNS,
    STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
};
use aspis_core::transcript::Transcript;
use aspis_core::HashFn;
use aspis_statement::{
    atomic_state_only_registry::atomic_state_only_relation_free_mask_cells_v3,
    atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3,
    pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
        pool_v1_payment_relation_free_mask_cells_v1,
        pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
        pool_v1_withdrawal_copy_active_row_masks_compiled_v1,
    },
    state_only_copy_active_rows_v4, state_only_relation_free_mask_cells_v4,
    StateOnlyTraceFoundation, STATE_ONLY_POSEIDON_TRACE_ROWS,
};
use zeroize::Zeroize;

use crate::state_only_zerocheck::{
    prove_state_only_sumcheck_from_claim, StateOnlyZerocheckProveError, StateOnlyZerocheckTrace,
};

const MASK_SEED_DOMAIN: &[u8] = b"aspis:state-only:private-mask-seed:v1";
const MASK_EXPAND_DOMAIN: &[u8] = b"aspis:state-only:private-mask-expand:v1";
const VIEW_DOMAIN: &[u8] = b"aspis:state-only:complete-public-view:v1";
const MASK_SAMPLE_RETRY_LIMIT: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyMaskBuildError {
    ZeroPrivateEntropy,
    ReusedMaskNonce,
    MaskSampleExhausted,
    TraceShape,
    Layout,
}

/// The caller must back this with storage whose lifetime covers every proof
/// made under the same key. The in-memory implementation below is a test and
/// single-process helper, not a durable wallet database.
pub trait StateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool;
}

#[derive(Default)]
pub struct InMemoryStateOnlyMaskNonceStore {
    seen: BTreeSet<([u8; 32], [u8; 32])>,
}

impl StateOnlyMaskNonceStore for InMemoryStateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        self.seen.insert((statement_digest, mask_nonce))
    }
}

pub struct StateOnlyMaskMaterial {
    c1: Vec<M31>,
    mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: Vec<QM31>,
    h1_padding: Vec<QM31>,
    pub mask_nonce: [u8; 32],
}

fn volatile_clear<T: Copy>(values: &mut [T], zero: T) {
    // pv-rw-a (extraction rewrite): counted loop; the volatile store itself is
    // in `volatile_store`, the one opaque helper. Same stores, same order,
    // same fence.
    let mut index = 0;
    while index < values.len() {
        volatile_store(&mut values[index], zero);
        index += 1;
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// OPAQUE IN EXTRACTION (pv-rw-a). Contract: performs exactly one volatile
/// write of `zero` to `*slot` (`core::ptr::write_volatile`) and has no other
/// effect; it returns nothing and cannot fail. The model treats it as
/// `*slot := zero`. It must stay a single volatile store so the compiler
/// cannot elide the zeroisation.
#[inline(always)]
fn volatile_store<T: Copy>(slot: &mut T, zero: T) {
    // SAFETY: `slot` is a unique borrow of initialised attempt-owned storage.
    unsafe { core::ptr::write_volatile(slot, zero) };
}

/// Pin body of `volatile_clear` (4bb3b3f), kept only for the
/// rewrite-equivalence test.
#[cfg(test)]
fn volatile_clear_pin<T: Copy>(values: &mut [T], zero: T) {
    for value in values {
        // SAFETY: callers pass uniquely borrowed attempt-owned storage.
        unsafe { core::ptr::write_volatile(value, zero) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

impl Drop for StateOnlyMaskMaterial {
    fn drop(&mut self) {
        volatile_clear(&mut self.c1, M31::ZERO);
        for column in &mut self.mask_only_c1 {
            volatile_clear(column, M31::ZERO);
        }
        volatile_clear(&mut self.g, QM31::ZERO);
        volatile_clear(&mut self.h1_padding, QM31::ZERO);
        self.mask_nonce.zeroize();
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AppliedStateOnlyMasks {
    /// Ten full-domain M31 columns committed after semantic C1 columns 0..15.
    pub mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    pub g: Vec<QM31>,
    /// Random only on rows absent from every copy endpoint. Its inactive
    /// sum is zero. The caller adds it to the uniquely determined copy helper
    /// after `lambda,chi`.
    pub h1_padding: Vec<QM31>,
    pub mask_nonce: [u8; 32],
}

impl Drop for AppliedStateOnlyMasks {
    fn drop(&mut self) {
        for column in &mut self.mask_only_c1 {
            volatile_clear(column, M31::ZERO);
        }
        volatile_clear(&mut self.g, QM31::ZERO);
        volatile_clear(&mut self.h1_padding, QM31::ZERO);
        self.mask_nonce.zeroize();
    }
}

fn copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows(state_only_copy_active_rows_v4())
}

fn active_rows(rows: &[u16]) -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    // pv-rw-a (extraction rewrite): counted loop in place of `for &row in rows`.
    let mut active = [false; STATE_ONLY_POSEIDON_TRACE_ROWS];
    let mut index = 0;
    while index < rows.len() {
        active[usize::from(rows[index])] = true;
        index += 1;
    }
    active
}

/// Pin body of `active_rows` (4bb3b3f), kept only for the rewrite-equivalence
/// test.
#[cfg(test)]
fn active_rows_pin(rows: &[u16]) -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    let mut active = [false; STATE_ONLY_POSEIDON_TRACE_ROWS];
    for &row in rows {
        active[usize::from(row)] = true;
    }
    active
}

fn atomic_copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows(atomic_state_only_copy_active_rows_v3())
}

fn active_rows_from_masks(masks: &[u16; 64]) -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    core::array::from_fn(|row| masks[row >> 4] & (1 << (row & 15)) != 0)
}

fn pool_v1_private_transfer_copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows_from_masks(pool_v1_private_transfer_copy_active_row_masks_compiled_v1())
}

fn pool_v1_withdrawal_copy_active_rows() -> [bool; STATE_ONLY_POSEIDON_TRACE_ROWS] {
    active_rows_from_masks(pool_v1_withdrawal_copy_active_row_masks_compiled_v1())
}

fn pool_v1_pair_forest_copy_active_rows(
) -> Result<[bool; STATE_ONLY_POSEIDON_TRACE_ROWS], StateOnlyMaskBuildError> {
    pool_v1_pair_forest_copy_active_rows_v1()
        .map(|rows| active_rows(&rows))
        .map_err(|_| StateOnlyMaskBuildError::Layout)
}

fn first_inactive_row(active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS]) -> usize {
    (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
        .find(|row| !active[*row])
        .expect("generated layout has an inactive row")
}

fn balance_m31_copy_inactive(
    table: &mut [M31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    // pv-aspis-rw (extraction rewrite, behaviour unchanged): counted loop in
    // place of the range/filter/fold chain; same rows, same order, same `add`
    // (evidence/pv-aspis-rewrite-20261111/notes/03-apply_mask_material.md).
    let sum = inactive_m31_sum_except(table, active, dependent);
    table[dependent] = M31::ZERO.sub(sum);
    Ok(())
}

/// pv-aspis-rw: sum, in row order, of `table[row]` over rows that are inactive
/// and not `dependent` (the pin's range/filter/fold). `table` has
/// `STATE_ONLY_POSEIDON_TRACE_ROWS` entries.
fn inactive_m31_sum_except(
    table: &[M31],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
    dependent: usize,
) -> M31 {
    let mut sum = M31::ZERO;
    let mut row = 0;
    while row < STATE_ONLY_POSEIDON_TRACE_ROWS {
        sum = inactive_m31_sum_except_step(sum, active[row], row, dependent, table);
        row += 1;
    }
    sum
}

/// pv-aspis-rw: one row of `inactive_m31_sum_except`; the branch lives here so
/// the loop body is straight-line, and `table[row]` is read only for the rows
/// the pin's `filter` let through.
fn inactive_m31_sum_except_step(
    sum: M31,
    is_active: bool,
    row: usize,
    dependent: usize,
    table: &[M31],
) -> M31 {
    if !is_active && row != dependent {
        sum.add(table[row])
    } else {
        sum
    }
}

/// Pin body of `balance_m31_copy_inactive` (c7593d23fdc), kept only for the
/// rewrite-equivalence test and for the other pin bodies.
#[cfg(test)]
fn balance_m31_copy_inactive_pin(
    table: &mut [M31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum = (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
        .filter(|row| !active[*row] && *row != dependent)
        .fold(M31::ZERO, |sum, row| sum.add(table[row]));
    table[dependent] = M31::ZERO.sub(sum);
    Ok(())
}

fn balance_qm31_copy_inactive(
    table: &mut [QM31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum = (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
        .filter(|row| !active[*row] && *row != dependent)
        .fold(QM31::ZERO, |sum, row| sum.add(table[row]));
    table[dependent] = QM31::ZERO.sub(sum);
    Ok(())
}

pub fn state_only_copy_inactive_sum_qm31(table: &[QM31]) -> Option<QM31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        let active = copy_active_rows();
        table
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

pub fn state_only_copy_inactive_sum_m31(table: &[M31]) -> Option<M31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        let active = copy_active_rows();
        table
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

pub fn state_only_padding_sum_m31(table: &[M31]) -> Option<M31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        table[STATE_ONLY_H1_PADDING_MASK_START..STATE_ONLY_H1_PADDING_MASK_END]
            .iter()
            .copied()
            .fold(M31::ZERO, M31::add)
    })
}

pub fn state_only_padding_sum_qm31(table: &[QM31]) -> Option<QM31> {
    (table.len() == STATE_ONLY_POSEIDON_TRACE_ROWS).then(|| {
        table[STATE_ONLY_H1_PADDING_MASK_START..STATE_ONLY_H1_PADDING_MASK_END]
            .iter()
            .copied()
            .fold(QM31::ZERO, QM31::add)
    })
}

pub fn apply_state_only_h1_padding_mask(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &copy_active_rows())
}

fn apply_h1_padding_mask_for_active(
    h1: &mut [QM31],
    padding: &[QM31],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    // pv-rw-a (extraction rewrite): counted loops in place of the
    // zip/any, enumerate/filter/fold and iter_mut/zip chains. The checks run
    // in the pin's order and the inactive sum is evaluated only when the
    // lengths and the active-row check pass, as with the pin's `||`. The
    // active-row check scans all rows instead of stopping at the first
    // violation (it removes an early exit on the reject path; it adds none).
    if h1.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || padding.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    if any_active_row_masked(padding, active) {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    if !qm31_is_zero(inactive_qm31_rows_sum(padding, active)) {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    add_qm31_rows(h1, padding);
    Ok(())
}

/// pv-rw-a: `true` iff some active row of `padding` is non-zero (the pin's
/// zip/any, without its early exit). `padding` has ROWS entries.
fn any_active_row_masked(padding: &[QM31], active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS]) -> bool {
    let mut masked = false;
    let mut row = 0;
    while row < STATE_ONLY_POSEIDON_TRACE_ROWS {
        masked = any_active_row_masked_step(masked, active[row], padding[row]);
        row += 1;
    }
    masked
}

/// pv-rw-a: one row of `any_active_row_masked` (branch outside the loop).
fn any_active_row_masked_step(masked: bool, is_active: bool, value: QM31) -> bool {
    if is_active && !qm31_is_zero(value) {
        true
    } else {
        masked
    }
}

/// pv-rw-a: sum, in row order, of the inactive rows of `table` (the pin's
/// enumerate/filter/fold). `table` has ROWS entries.
fn inactive_qm31_rows_sum(table: &[QM31], active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS]) -> QM31 {
    let mut sum = QM31::ZERO;
    let mut row = 0;
    while row < STATE_ONLY_POSEIDON_TRACE_ROWS {
        sum = inactive_qm31_rows_sum_step(sum, active[row], table[row]);
        row += 1;
    }
    sum
}

/// pv-rw-a: one row of `inactive_qm31_rows_sum` (branch outside the loop).
fn inactive_qm31_rows_sum_step(sum: QM31, is_active: bool, value: QM31) -> QM31 {
    if !is_active {
        sum.add(value)
    } else {
        sum
    }
}

/// pv-rw-a: `target[row] += mask[row]` for every row (the pin's iter_mut/zip
/// loop; both slices have ROWS entries).
fn add_qm31_rows(target: &mut [QM31], mask: &[QM31]) {
    let mut row = 0;
    while row < STATE_ONLY_POSEIDON_TRACE_ROWS {
        target[row] = target[row].add(mask[row]);
        row += 1;
    }
}

/// pv-rw-a: `value == QM31::ZERO` (derived `PartialEq`), outside any loop.
fn qm31_is_zero(value: QM31) -> bool {
    value == QM31::ZERO
}

/// Pin body of `apply_h1_padding_mask_for_active` (4bb3b3f), kept only for the
/// rewrite-equivalence test.
#[cfg(test)]
fn apply_h1_padding_mask_for_active_pin(
    h1: &mut [QM31],
    padding: &[QM31],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    if h1.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || padding.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || active
            .iter()
            .copied()
            .zip(padding)
            .any(|(active, value)| active && *value != QM31::ZERO)
        || padding
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
            != QM31::ZERO
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    for (value, mask) in h1.iter_mut().zip(padding) {
        *value = value.add(*mask);
    }
    Ok(())
}

pub fn apply_atomic_state_only_h1_padding_mask_v3(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &atomic_copy_active_rows())
}

pub fn apply_pool_v1_private_transfer_h1_padding_mask_v1(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &pool_v1_private_transfer_copy_active_rows())
}

pub fn apply_pool_v1_withdrawal_h1_padding_mask_v1(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &pool_v1_withdrawal_copy_active_rows())
}

pub fn apply_pool_v1_pair_forest_h1_padding_mask_v1(
    h1: &mut [QM31],
    padding: &[QM31],
) -> Result<(), StateOnlyMaskBuildError> {
    apply_h1_padding_mask_for_active(h1, padding, &pool_v1_pair_forest_copy_active_rows()?)
}

#[cfg(test)]
#[path = "r11_mask_material_kat.rs"]
mod r11_mask_material_kat;

#[cfg(test)]
#[path = "r13_source_bridge.rs"]
mod r13_source_bridge;

struct SeedExpander {
    hash: HashFn,
    seed: [u8; 32],
    counter: u64,
    block: [u8; 32],
    word: usize,
}

impl Drop for SeedExpander {
    fn drop(&mut self) {
        self.seed.zeroize();
        self.block.zeroize();
        self.counter.zeroize();
        self.word.zeroize();
    }
}

impl SeedExpander {
    fn new(hash: HashFn, seed: [u8; 32]) -> Self {
        Self {
            hash,
            seed,
            counter: 0,
            block: [0; 32],
            word: 8,
        }
    }

    #[cfg_attr(kani, kani::requires(self.word <= 8))]
    #[cfg_attr(kani, kani::requires(self.hash == crate::HOST_HASH))]
    #[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::expander_domain(
        b"aspis:state-only:private-mask-expand:v1", self.seed, self.counter, self.word)))]
    #[cfg_attr(kani, kani::modifies(&mut self.counter, &mut self.block, &mut self.word))]
    #[cfg_attr(kani, kani::ensures(|result| crate::prover_commit_reference::next_matches(
        b"aspis:state-only:private-mask-expand:v1",
        crate::prover_commit_reference::State { seed: old(self.seed), counter: old(self.counter), block: old(self.block), word: old(self.word) },
        *result,
        crate::prover_commit_reference::State { seed: self.seed, counter: self.counter, block: self.block, word: self.word })))]
    fn next_word(&mut self) -> u32 {
        if self.word == 8 {
            self.block = state_only_mask_expander_block(self.hash, self.seed, self.counter);
            self.counter = self.counter.wrapping_add(1);
            self.word = 0;
        }
        let start = 4 * self.word;
        self.word += 1;
        u32::from_le_bytes(self.block[start..start + 4].try_into().unwrap())
    }

    fn m31(&mut self) -> Result<M31, StateOnlyMaskBuildError> {
        for _ in 0..MASK_SAMPLE_RETRY_LIMIT {
            let candidate = self.next_word() & 0x7fff_ffff;
            if candidate < P {
                return Ok(M31(candidate));
            }
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }

    fn qm31(&mut self) -> Result<QM31, StateOnlyMaskBuildError> {
        Ok(QM31 {
            c0: CM31::new(self.m31()?, self.m31()?),
            c1: CM31::new(self.m31()?, self.m31()?),
        })
    }
}

/// Derive a private one-time seed. `precommit_binding` is public transcript
/// state; secrecy comes exclusively from `private_entropy`.
pub fn derive_state_only_mask_seed(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
) -> Result<[u8; 32], StateOnlyMaskBuildError> {
    let result = derive_state_only_mask_seed_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
    );
    private_entropy.zeroize();
    result
}

fn derive_state_only_mask_seed_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
) -> Result<[u8; 32], StateOnlyMaskBuildError> {
    if *private_entropy == [0; 32] {
        return Err(StateOnlyMaskBuildError::ZeroPrivateEntropy);
    }
    Ok(hash(&[
        MASK_SEED_DOMAIN,
        &precommit_binding,
        &context.encode(),
        private_entropy,
    ]))
}

pub fn build_state_only_mask_material(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = state_only_relation_free_mask_cells_v4()
        .map_err(|_| StateOnlyMaskBuildError::Layout)
        .and_then(|cells| {
            build_mask_material_for_layout(
                hash,
                precommit_binding,
                context,
                &private_entropy,
                nonce_store,
                &cells,
                &copy_active_rows(),
            )
        });
    private_entropy.zeroize();
    result
}

fn build_mask_material_for_layout(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
        return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
    }
    let seed = derive_state_only_mask_seed_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        private_entropy,
    )?;
    let mut expander = SeedExpander::new(hash, seed);
    let inactive_dependent = first_inactive_row(active);
    // pv-rw-a (extraction rewrite): the four mask samplers are named
    // functions (sample_mask_cells / _columns / _g / _h1_padding), each with
    // its loops in counted-loop helpers.
    // DRAW ORDER (unchanged from the pin), all from this one SeedExpander:
    //   1. sample_mask_cells: cells.len() m31 draws, cell order (c1);
    //   2. sample_mask_columns: for each of the 10 mask-only columns in order,
    //      1024 m31 draws in row order (the dependent row's draw is drawn and
    //      then overwritten by the balance), then that column's balance;
    //   3. sample_mask_g: 1024 qm31 draws in row order (dependent row drawn
    //      and overwritten), then the balance;
    //   4. sample_mask_h1_padding: one qm31 draw per row that is inactive and
    //      not the dependent row, in row order (active rows and the dependent
    //      row are NOT drawn), then the balance.
    // Each m31 draw is rejection-sampled (at most 16 words); each qm31 is four
    // m31 draws. The first error (sampling or balance) is returned, as with
    // the pin's `?`.
    let c1 = sample_mask_cells(&mut expander, cells.len())?;
    let mask_only_c1 = sample_mask_columns(&mut expander, active, inactive_dependent)?;
    let g = sample_mask_g(&mut expander, active, inactive_dependent)?;
    let h1_padding = sample_mask_h1_padding(&mut expander, active, inactive_dependent)?;
    Ok(StateOnlyMaskMaterial {
        c1,
        mask_only_c1,
        g,
        h1_padding,
        mask_nonce: context.mask_nonce,
    })
}

/// pv-rw-a: appends `count` m31 draws to `values`, in order; the first
/// sampling error is returned (draws made so far stay in `values`).
fn sample_m31_into(
    expander: &mut SeedExpander,
    values: &mut Vec<M31>,
    count: usize,
) -> Result<(), StateOnlyMaskBuildError> {
    let mut index = 0;
    while index < count {
        let value = expander.m31()?;
        values.push(value);
        index += 1;
    }
    Ok(())
}

/// pv-rw-a: appends `count` qm31 draws to `values`, in order; the first
/// sampling error is returned (draws made so far stay in `values`).
fn sample_qm31_into(
    expander: &mut SeedExpander,
    values: &mut Vec<QM31>,
    count: usize,
) -> Result<(), StateOnlyMaskBuildError> {
    let mut index = 0;
    while index < count {
        let value = expander.qm31()?;
        values.push(value);
        index += 1;
    }
    Ok(())
}

/// pv-rw-a: mask draw 1 (C1 relation-free cells): `count` m31 draws in cell
/// order.
fn sample_mask_cells(
    expander: &mut SeedExpander,
    count: usize,
) -> Result<Vec<M31>, StateOnlyMaskBuildError> {
    let mut c1 = Vec::with_capacity(count);
    sample_m31_into(expander, &mut c1, count)?;
    Ok(c1)
}

/// pv-rw-a: mask draw 2 (mask-only C1 columns): `sample_mask_column` for
/// columns 0..9 in order. Unrolled with an array literal: the counted loop
/// assigning into the array (local, and then borrowed) did not extract
/// ("Could not match the contexts", runs r3/r4).
fn sample_mask_columns(
    expander: &mut SeedExpander,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
    dependent: usize,
) -> Result<[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], StateOnlyMaskBuildError> {
    const _: () = assert!(STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS == 10);
    let column0 = sample_mask_column(expander, active, dependent)?;
    let column1 = sample_mask_column(expander, active, dependent)?;
    let column2 = sample_mask_column(expander, active, dependent)?;
    let column3 = sample_mask_column(expander, active, dependent)?;
    let column4 = sample_mask_column(expander, active, dependent)?;
    let column5 = sample_mask_column(expander, active, dependent)?;
    let column6 = sample_mask_column(expander, active, dependent)?;
    let column7 = sample_mask_column(expander, active, dependent)?;
    let column8 = sample_mask_column(expander, active, dependent)?;
    let column9 = sample_mask_column(expander, active, dependent)?;
    Ok([
        column0, column1, column2, column3, column4, column5, column6, column7, column8, column9,
    ])
}

/// pv-rw-a: one mask-only column: 1024 m31 draws in row order, then its
/// inactive-row balance (overwrites the dependent row).
fn sample_mask_column(
    expander: &mut SeedExpander,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
    dependent: usize,
) -> Result<Vec<M31>, StateOnlyMaskBuildError> {
    let mut values = Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS);
    sample_m31_into(expander, &mut values, STATE_ONLY_POSEIDON_TRACE_ROWS)?;
    balance_m31_copy_inactive(&mut values, dependent, active)?;
    Ok(values)
}

/// pv-rw-a: mask draw 3 (G): 1024 qm31 draws in row order, then the
/// inactive-row balance (overwrites the dependent row).
fn sample_mask_g(
    expander: &mut SeedExpander,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
    dependent: usize,
) -> Result<Vec<QM31>, StateOnlyMaskBuildError> {
    let mut g = Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS);
    sample_qm31_into(expander, &mut g, STATE_ONLY_POSEIDON_TRACE_ROWS)?;
    balance_qm31_copy_inactive(&mut g, dependent, active)?;
    Ok(g)
}

/// pv-rw-a: mask draw 4 (H1 padding): one qm31 draw per row that is inactive
/// and not `dependent`, in row order (other rows stay zero, not drawn), then
/// the inactive-row balance.
fn sample_mask_h1_padding(
    expander: &mut SeedExpander,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
    dependent: usize,
) -> Result<Vec<QM31>, StateOnlyMaskBuildError> {
    // Built by pushing row values 0..1023 in order; rows that are not drawn
    // get QM31::ZERO, exactly the pin's `vec![ZERO; ROWS]` entries.
    let h1_padding = sample_mask_h1_padding_from(
        expander,
        Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS),
        0,
        active,
        dependent,
    )?;
    let mut h1_padding = h1_padding;
    balance_qm31_copy_inactive(&mut h1_padding, dependent, active)?;
    Ok(h1_padding)
}

/// pv-rw-a: rows `row..ROWS` of `sample_mask_h1_padding`, by structural
/// recursion on the row index with the vector moved through the calls (the
/// counted-loop forms did not extract: runs r2-r6). Pushes one value per row
/// in row order; the first sampling error is returned. Recursion depth is at
/// most ROWS = 1024 small frames.
fn sample_mask_h1_padding_from(
    expander: &mut SeedExpander,
    mut values: Vec<QM31>,
    row: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
    dependent: usize,
) -> Result<Vec<QM31>, StateOnlyMaskBuildError> {
    if row >= STATE_ONLY_POSEIDON_TRACE_ROWS {
        return Ok(values);
    }
    let value = sample_mask_h1_padding_row(expander, row, active[row], dependent)?;
    values.push(value);
    sample_mask_h1_padding_from(expander, values, row + 1, active, dependent)
}

/// pv-rw-a: one row of `sample_mask_h1_padding` (branch outside the loop):
/// a fresh qm31 draw for an inactive non-dependent row; otherwise
/// QM31::ZERO with no draw.
fn sample_mask_h1_padding_row(
    expander: &mut SeedExpander,
    row: usize,
    is_active: bool,
    dependent: usize,
) -> Result<QM31, StateOnlyMaskBuildError> {
    if !is_active && row != dependent {
        expander.qm31()
    } else {
        Ok(QM31::ZERO)
    }
}

/// Pin body of `build_mask_material_for_layout` (4bb3b3f), kept only for the rewrite-equivalence
/// test.
#[cfg(test)]
fn build_mask_material_for_layout_pin(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
        return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
    }
    let seed = derive_state_only_mask_seed_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        private_entropy,
    )?;
    let mut expander = SeedExpander::new(hash, seed);
    let inactive_dependent = first_inactive_row(active);
    let mut c1 = Vec::with_capacity(cells.len());
    for _ in 0..cells.len() {
        c1.push(expander.m31()?);
    }
    let mut mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
        core::array::from_fn(|_| Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));
    for column in &mut mask_only_c1 {
        for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
            column.push(expander.m31()?);
        }
        balance_m31_copy_inactive_pin(column, inactive_dependent, active)?;
    }
    let mut g = Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS);
    for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        g.push(expander.qm31()?);
    }
    balance_qm31_copy_inactive(&mut g, inactive_dependent, active)?;
    let mut h1_padding = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
    for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        if !active[row] && row != inactive_dependent {
            h1_padding[row] = expander.qm31()?;
        }
    }
    balance_qm31_copy_inactive(&mut h1_padding, inactive_dependent, active)?;
    Ok(StateOnlyMaskMaterial {
        c1,
        mask_only_c1,
        g,
        h1_padding,
        mask_nonce: context.mask_nonce,
    })
}

pub fn build_atomic_state_only_mask_material_v3(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_atomic_state_only_mask_material_v3_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

pub(crate) fn build_atomic_state_only_mask_material_v3_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    build_mask_material_for_layout(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        &cells,
        &atomic_copy_active_rows(),
    )
}

fn build_pool_v1_payment_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    expected_factor_fingerprint: u64,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if context.mask_layout_fingerprint != PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
        || context.layout_factor_fingerprint != expected_factor_fingerprint
    {
        return Err(StateOnlyMaskBuildError::Layout);
    }
    let cells = pool_v1_payment_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    build_mask_material_for_layout(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        &cells,
        active,
    )
}

pub(crate) fn build_pool_v1_private_transfer_mask_material_v1_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    build_pool_v1_payment_mask_material_v1(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        &pool_v1_private_transfer_copy_active_rows(),
    )
}

pub(crate) fn build_pool_v1_withdrawal_mask_material_v1_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    build_pool_v1_payment_mask_material_v1(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT,
        &pool_v1_withdrawal_copy_active_rows(),
    )
}

pub fn build_pool_v1_private_transfer_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_pool_v1_private_transfer_mask_material_v1_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

pub fn build_pool_v1_withdrawal_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_pool_v1_withdrawal_mask_material_v1_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

pub(crate) fn build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if context.mask_layout_fingerprint
        != PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
        || context.layout_factor_fingerprint
            != PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
    {
        return Err(StateOnlyMaskBuildError::Layout);
    }
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    build_mask_material_for_layout(
        hash,
        precommit_binding,
        context,
        private_entropy,
        nonce_store,
        &cells,
        &pool_v1_pair_forest_copy_active_rows()?,
    )
}

pub fn build_pool_v1_pair_forest_mask_material_v1(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    mut private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    let result = build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        &private_entropy,
        nonce_store,
    );
    private_entropy.zeroize();
    result
}

/// Consume the one-time material while applying it, making accidental reuse
/// through this API impossible without reconstructing material from a reused
/// nonce (which the nonce store rejects).
pub fn apply_state_only_mask_material(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells =
        state_only_relation_free_mask_cells_v4().map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(trace, material, &cells, &copy_active_rows())
}

/// pv-aspis-rw: for every C1 column, the row of the last cell of `cells` (in
/// order) that lies in that column on an inactive row, or `None` (the pin's
/// `for cell in cells` loop of `apply_mask_material_for_layout`).
fn inactive_dependent_rows(
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> [Option<usize>; STATE_ONLY_HIDING_C1_COLUMNS] {
    let mut inactive_dependents = [None; STATE_ONLY_HIDING_C1_COLUMNS];
    let mut index = 0;
    while index < cells.len() {
        inactive_dependent_rows_step(&mut inactive_dependents, cells[index], active);
        index += 1;
    }
    inactive_dependents
}

/// pv-aspis-rw: one cell of `inactive_dependent_rows` (branch outside the
/// loop): row and column are read, `active[row]` is tested, and only for an
/// inactive row is the column's entry written, in that order, as in the pin.
fn inactive_dependent_rows_step(
    inactive_dependents: &mut [Option<usize>; STATE_ONLY_HIDING_C1_COLUMNS],
    cell: aspis_statement::TraceCell,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) {
    let row = usize::from(cell.row);
    let column = usize::from(cell.column);
    if !active[row] {
        inactive_dependents[column] = Some(row);
    }
}

/// pv-aspis-rw: the first loop of `apply_mask_material_for_layout`: mask
/// `index` is added to cell `index`, in order. `masks` has `cells.len()`
/// entries (checked by the caller) and is released on return.
fn add_cell_masks(
    trace: &mut StateOnlyTraceFoundation,
    cells: &[aspis_statement::TraceCell],
    masks: Vec<M31>,
) {
    let mut index = 0;
    while index < cells.len() {
        add_cell_mask(trace, cells[index], masks[index]);
        index += 1;
    }
}

/// pv-aspis-rw: the second loop of `apply_mask_material_for_layout`: every C1
/// column, in order, is balanced on its dependent row; the first failure is
/// returned with the earlier columns already balanced. Every entry of
/// `dependents` is `Some` (checked by the caller).
fn balance_trace_columns(
    trace: &mut StateOnlyTraceFoundation,
    dependents: &[Option<usize>; STATE_ONLY_HIDING_C1_COLUMNS],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    let mut column = 0;
    while column < STATE_ONLY_HIDING_C1_COLUMNS {
        balance_m31_copy_inactive(&mut trace.c1[column], dependents[column].unwrap(), active)?;
        column += 1;
    }
    Ok(())
}

/// pv-aspis-rw: `trace.c1[cell.column][cell.row] += mask`, one step of the
/// loop of `add_cell_masks` (column indexed before row,
/// as in the pin).
fn add_cell_mask(trace: &mut StateOnlyTraceFoundation, cell: aspis_statement::TraceCell, mask: M31) {
    let column = usize::from(cell.column);
    let row = usize::from(cell.row);
    trace.c1[column][row] = trace.c1[column][row].add(mask);
}

// pv-aspis-rw: the counted column loop of `balance_trace_columns`
// relies on the trace having exactly as many C1 columns as the hiding layout.
const _: () = assert!(
    aspis_statement::state_only_trace::STATE_ONLY_C1_COLUMNS == STATE_ONLY_HIDING_C1_COLUMNS
);

fn apply_mask_material_for_layout(
    trace: &mut StateOnlyTraceFoundation,
    mut material: StateOnlyMaskMaterial,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    if trace
        .c1
        .iter()
        .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    if material.c1.len() != cells.len()
        || material
            .mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || material.g.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || material.h1_padding.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    // pv-aspis-rw (extraction rewrite, behaviour unchanged): the loop
    // `for cell in cells` that records, per column, the row of its last
    // inactive cell is the counted loop of `inactive_dependent_rows`.
    let inactive_dependents = inactive_dependent_rows(cells, active);
    // pv-rw-a (extraction rewrite): closure in place of the `Option::is_none`
    // function item (the closure form of `any` above extracts).
    if inactive_dependents
        .iter()
        .any(|dependent| dependent.is_none())
    {
        return Err(StateOnlyMaskBuildError::Layout);
    }
    // pv-aspis-rw (extraction rewrite, behaviour unchanged): the two loops
    // `for (cell, mask) in cells.iter().copied().zip(take(c1))` and
    // `for (column, dependent) in trace.c1.iter_mut().zip(inactive_dependents)`
    // are the counted loops of `add_cell_masks` and `balance_trace_columns`.
    // The masks are taken out of `material` as before and released when the
    // first loop is over, as the pin's consumed iterator was;
    // `material.c1.len() == cells.len()` was checked above, so the zip had
    // exactly `cells.len()` items; `trace.c1` and `inactive_dependents` both
    // have STATE_ONLY_HIDING_C1_COLUMNS entries
    // (evidence/pv-aspis-rewrite-20261111/notes/03-apply_mask_material.md).
    add_cell_masks(trace, cells, core::mem::take(&mut material.c1));
    balance_trace_columns(trace, &inactive_dependents, active)?;
    Ok(AppliedStateOnlyMasks {
        mask_only_c1: core::mem::take(&mut material.mask_only_c1),
        g: core::mem::take(&mut material.g),
        h1_padding: core::mem::take(&mut material.h1_padding),
        mask_nonce: material.mask_nonce,
    })
}

/// Pin body of `apply_mask_material_for_layout` (4bb3b3f), kept only for the rewrite-equivalence
/// test.
#[cfg(test)]
fn apply_mask_material_for_layout_pin(
    trace: &mut StateOnlyTraceFoundation,
    mut material: StateOnlyMaskMaterial,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    if trace
        .c1
        .iter()
        .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    if material.c1.len() != cells.len()
        || material
            .mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || material.g.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
        || material.h1_padding.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut inactive_dependents = [None; STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        let row = usize::from(cell.row);
        let column = usize::from(cell.column);
        if !active[row] {
            inactive_dependents[column] = Some(row);
        }
    }
    if inactive_dependents.iter().any(Option::is_none) {
        return Err(StateOnlyMaskBuildError::Layout);
    }
    for (cell, mask) in cells.iter().copied().zip(core::mem::take(&mut material.c1)) {
        let value = &mut trace.c1[usize::from(cell.column)][usize::from(cell.row)];
        *value = value.add(mask);
    }
    for (column, dependent) in trace.c1.iter_mut().zip(inactive_dependents) {
        balance_m31_copy_inactive_pin(column, dependent.unwrap(), active)?;
    }
    Ok(AppliedStateOnlyMasks {
        mask_only_c1: core::mem::take(&mut material.mask_only_c1),
        g: core::mem::take(&mut material.g),
        h1_padding: core::mem::take(&mut material.h1_padding),
        mask_nonce: material.mask_nonce,
    })
}

pub fn apply_atomic_state_only_mask_material_v3(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(trace, material, &cells, &atomic_copy_active_rows())
}

pub fn apply_pool_v1_private_transfer_mask_material_v1(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = pool_v1_payment_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(
        trace,
        material,
        &cells,
        &pool_v1_private_transfer_copy_active_rows(),
    )
}

pub fn apply_pool_v1_withdrawal_mask_material_v1(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = pool_v1_payment_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(
        trace,
        material,
        &cells,
        &pool_v1_withdrawal_copy_active_rows(),
    )
}

pub fn apply_pool_v1_pair_forest_mask_material_v1(
    trace: &mut StateOnlyTraceFoundation,
    material: StateOnlyMaskMaterial,
) -> Result<AppliedStateOnlyMasks, StateOnlyMaskBuildError> {
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1()
        .map_err(|_| StateOnlyMaskBuildError::Layout)?;
    apply_mask_material_for_layout(
        trace,
        material,
        &cells,
        &pool_v1_pair_forest_copy_active_rows()?,
    )
}

fn evaluate_m31_table(
    table: &[M31],
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut layer = table
        .iter()
        .copied()
        .map(|value| QM31::from_cm31(CM31::from_m31(value)))
        .collect::<Vec<_>>();
    for coordinate in point.iter().rev() {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            next.push(pair[0].add(coordinate.mul(pair[1].sub(pair[0]))));
        }
        layer = next;
    }
    Ok(layer[0])
}

fn evaluate_qm31_table(
    table: &[QM31],
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut layer = table.to_vec();
    for coordinate in point.iter().rev() {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            next.push(pair[0].add(coordinate.mul(pair[1].sub(pair[0]))));
        }
        layer = next;
    }
    Ok(layer[0])
}

pub fn state_only_mask_oracle_value(
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if trace.c1.len() != STATE_ONLY_HIDING_C1_COLUMNS
        || trace
            .c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let c1: [QM31; STATE_ONLY_HIDING_C1_COLUMNS] =
        core::array::from_fn(|column| evaluate_m31_table(&trace.c1[column], point).unwrap());
    let mask_only_c1 =
        core::array::from_fn(|column| evaluate_m31_table(&mask_only_c1[column], point).unwrap());
    Ok(state_only_selected_mask_value(
        &c1,
        &mask_only_c1,
        evaluate_qm31_table(g, point)?,
        point,
    ))
}

pub fn state_only_initial_mask_claim(
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
) -> Result<QM31, StateOnlyMaskBuildError> {
    if trace
        .c1
        .iter()
        .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || mask_only_c1
            .iter()
            .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
        || g.len() != STATE_ONLY_POSEIDON_TRACE_ROWS
    {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let mut claim = QM31::ZERO;
    for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        let point = core::array::from_fn(|coordinate| {
            if (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1 == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        });
        let c1 =
            core::array::from_fn(|column| QM31::from_cm31(CM31::from_m31(trace.c1[column][row])));
        let mask_only_c1 = core::array::from_fn(|column| {
            QM31::from_cm31(CM31::from_m31(mask_only_c1[column][row]))
        });
        claim = claim.add(state_only_selected_mask_value(
            &c1,
            &mask_only_c1,
            g[row],
            &point,
        ));
    }
    Ok(claim)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskedStateOnlyZerocheckTrace {
    pub initial_mask_claim: QM31,
    pub eta: QM31,
    pub sumcheck: StateOnlyZerocheckTrace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MaskedStateOnlyZerocheckError<E> {
    RootsNotBound,
    Mask(StateOnlyMaskBuildError),
    Schedule(StateOnlyHidingScheduleError),
    Sumcheck(StateOnlyZerocheckProveError<E>),
}

/// Prove `H + eta*F`, where the caller has already absorbed every masked root
/// after `precommit_binding`. The honest unmasked zerocheck claim is zero, so
/// the combined initial claim is exactly `sum(H)`.
pub fn prove_masked_state_only_zerocheck<F, E>(
    transcript: &mut Transcript,
    precommit_binding: [u8; 32],
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    mut original_oracle: F,
) -> Result<MaskedStateOnlyZerocheckTrace, MaskedStateOnlyZerocheckError<E>>
where
    F: FnMut(&[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    if transcript.diagnostic_state() == precommit_binding {
        return Err(MaskedStateOnlyZerocheckError::RootsNotBound);
    }
    let initial_mask_claim = state_only_initial_mask_claim(trace, mask_only_c1, g)
        .map_err(MaskedStateOnlyZerocheckError::Mask)?;
    let eta = begin_state_only_masked_sumcheck(transcript, initial_mask_claim)
        .map_err(MaskedStateOnlyZerocheckError::Schedule)?;
    let sumcheck = prove_state_only_sumcheck_from_claim(
        transcript,
        |point| {
            let mask = state_only_mask_oracle_value(trace, mask_only_c1, g, point)
                .map_err(MaskedStateOnlyZerocheckError::Mask)?;
            let original = original_oracle(point).map_err(|error| {
                MaskedStateOnlyZerocheckError::Sumcheck(StateOnlyZerocheckProveError::Oracle(error))
            })?;
            Ok::<_, MaskedStateOnlyZerocheckError<E>>(mask.add(eta.mul(original)))
        },
        initial_mask_claim,
    )
    .map_err(|error| match error {
        StateOnlyZerocheckProveError::Oracle(error) => error,
        other => MaskedStateOnlyZerocheckError::Sumcheck(match other {
            StateOnlyZerocheckProveError::BoundaryMismatch { round } => {
                StateOnlyZerocheckProveError::BoundaryMismatch { round }
            }
            StateOnlyZerocheckProveError::TerminalMismatch => {
                StateOnlyZerocheckProveError::TerminalMismatch
            }
            StateOnlyZerocheckProveError::ChallengeSampleExhausted => {
                StateOnlyZerocheckProveError::ChallengeSampleExhausted
            }
            StateOnlyZerocheckProveError::Oracle(_) => unreachable!(),
        }),
    })?;
    Ok(MaskedStateOnlyZerocheckTrace {
        initial_mask_claim,
        eta,
        sumcheck,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicAccountSnapshot {
    pub key: [u8; 32],
    pub owner: [u8; 32],
    pub lamports: u64,
    pub executable: bool,
    pub rent_epoch: u64,
    pub data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicAccountDelta {
    pub before: Option<PublicAccountSnapshot>,
    pub after: Option<PublicAccountSnapshot>,
}

/// Complete public surface for the candidate transaction. Parsed roots and
/// openings are kept even though they also occur in `proof_bytes`: the
/// explicit duplication makes omissions in distinguisher tests visible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyCompletePublicView {
    pub proof_bytes: Vec<u8>,
    pub roots: Vec<[u8; 32]>,
    pub openings: Vec<Vec<u8>>,
    pub statement_values: Vec<[u8; 16]>,
    pub program_logs: Vec<Vec<u8>>,
    pub state_delta: PublicAccountDelta,
    pub nullifier_delta: PublicAccountDelta,
    pub output_delta: PublicAccountDelta,
}

fn append_bytes(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    output.extend_from_slice(bytes);
}

fn append_snapshot(output: &mut Vec<u8>, snapshot: &Option<PublicAccountSnapshot>) {
    match snapshot {
        None => output.push(0),
        Some(snapshot) => {
            output.push(1);
            output.extend_from_slice(&snapshot.key);
            output.extend_from_slice(&snapshot.owner);
            output.extend_from_slice(&snapshot.lamports.to_le_bytes());
            output.push(u8::from(snapshot.executable));
            output.extend_from_slice(&snapshot.rent_epoch.to_le_bytes());
            append_bytes(output, &snapshot.data);
        }
    }
}

fn append_delta(output: &mut Vec<u8>, delta: &PublicAccountDelta) {
    append_snapshot(output, &delta.before);
    append_snapshot(output, &delta.after);
}

impl StateOnlyCompletePublicView {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut output = Vec::new();
        append_bytes(&mut output, VIEW_DOMAIN);
        append_bytes(&mut output, &self.proof_bytes);
        output.extend_from_slice(&(self.roots.len() as u64).to_le_bytes());
        for root in &self.roots {
            output.extend_from_slice(root);
        }
        output.extend_from_slice(&(self.openings.len() as u64).to_le_bytes());
        for opening in &self.openings {
            append_bytes(&mut output, opening);
        }
        output.extend_from_slice(&(self.statement_values.len() as u64).to_le_bytes());
        for value in &self.statement_values {
            output.extend_from_slice(value);
        }
        output.extend_from_slice(&(self.program_logs.len() as u64).to_le_bytes());
        for log in &self.program_logs {
            append_bytes(&mut output, log);
        }
        append_delta(&mut output, &self.state_delta);
        append_delta(&mut output, &self.nullifier_delta);
        append_delta(&mut output, &self.output_delta);
        output
    }

    pub fn digest(&self, hash: HashFn) -> [u8; 32] {
        hash(&[VIEW_DOMAIN, &self.canonical_bytes()])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HOST_HASH;
    use aspis_core::transcript::label;

    fn zero_trace() -> StateOnlyTraceFoundation {
        StateOnlyTraceFoundation {
            c1: core::array::from_fn(|_| vec![M31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS]),
        }
    }

    fn mask_context(nonce: u8) -> StateOnlyHidingContext {
        StateOnlyHidingContext::pinned([0x51; 32], [nonce; 32])
    }

    fn precommit(context: StateOnlyHidingContext) -> ([u8; 32], Transcript) {
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::STATEMENT, &context.statement_digest);
        let binding = begin_state_only_hiding_precommit(&mut transcript, context).unwrap();
        (binding, transcript)
    }

    fn pv_rw_a_random_bytes<const N: usize>() -> [u8; N] {
        let mut out = [0u8; N];
        getrandom::fill(&mut out).unwrap();
        out
    }

    fn pv_rw_a_random_qm31() -> QM31 {
        let bytes: [u8; 16] = pv_rw_a_random_bytes();
        let limb = |i: usize| M31(u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()) % P);
        QM31 {
            c0: CM31::new(limb(0), limb(1)),
            c1: CM31::new(limb(2), limb(3)),
        }
    }

    /// Host hash with three of eight words forced to reject, to exercise the
    /// rejection-sampling retry path.
    fn pv_rw_a_partly_rejecting_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut out = HOST_HASH(inputs);
        for byte in out.iter_mut().take(12) {
            *byte = 0xff;
        }
        out
    }

    fn pv_rw_a_rejecting_hash(_inputs: &[&[u8]]) -> [u8; 32] {
        [0xff; 32]
    }

    fn pv_rw_a_layouts() -> Vec<(Vec<aspis_statement::TraceCell>, [bool; STATE_ONLY_POSEIDON_TRACE_ROWS])> {
        vec![
            (
                state_only_relation_free_mask_cells_v4().unwrap(),
                copy_active_rows(),
            ),
            (
                atomic_state_only_relation_free_mask_cells_v3().unwrap(),
                atomic_copy_active_rows(),
            ),
            (
                pool_v1_payment_relation_free_mask_cells_v1().unwrap(),
                pool_v1_private_transfer_copy_active_rows(),
            ),
            (
                pool_v1_payment_relation_free_mask_cells_v1().unwrap(),
                pool_v1_withdrawal_copy_active_rows(),
            ),
            (
                pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap(),
                pool_v1_pair_forest_copy_active_rows().unwrap(),
            ),
        ]
    }

    #[test]
    fn pv_rw_a_active_rows_and_volatile_clear_match_pin_bodies() {
        let fixed: [&[u16]; 3] = [
            state_only_copy_active_rows_v4(),
            atomic_state_only_copy_active_rows_v3(),
            &[],
        ];
        for rows in fixed {
            assert_eq!(active_rows(rows), active_rows_pin(rows));
        }
        let forest = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        assert_eq!(active_rows(&forest), active_rows_pin(&forest));
        for _ in 0..64 {
            let bytes: [u8; 512] = pv_rw_a_random_bytes();
            let len = usize::from(bytes[0]);
            let rows: Vec<u16> = (0..len)
                .map(|i| u16::from_le_bytes([bytes[2 * i + 2], bytes[2 * i + 3]]) % 1024)
                .collect();
            assert_eq!(active_rows(&rows), active_rows_pin(&rows));
            let mut a: Vec<QM31> = (0..len).map(|_| pv_rw_a_random_qm31()).collect();
            let mut b = a.clone();
            volatile_clear(&mut a, QM31::ZERO);
            volatile_clear_pin(&mut b, QM31::ZERO);
            assert_eq!(a, b);
            assert!(a.iter().all(|value| *value == QM31::ZERO));
            let mut c: Vec<M31> = (0..len).map(|i| M31(u32::from(bytes[i]))).collect();
            let mut d = c.clone();
            volatile_clear(&mut c, M31(7));
            volatile_clear_pin(&mut d, M31(7));
            assert_eq!(c, d);
        }
    }

    #[test]
    fn pv_rw_a_h1_padding_matches_pin_body() {
        for (_, active) in pv_rw_a_layouts() {
            for case in 0..8 {
                let mut padding: Vec<QM31> = (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
                    .map(|row| if active[row] { QM31::ZERO } else { pv_rw_a_random_qm31() })
                    .collect();
                let dependent = first_inactive_row(&active);
                balance_qm31_copy_inactive(&mut padding, dependent, &active).unwrap();
                let mut h1: Vec<QM31> = (0..STATE_ONLY_POSEIDON_TRACE_ROWS)
                    .map(|_| pv_rw_a_random_qm31())
                    .collect();
                match case {
                    0 => {}
                    1 => {
                        let row = (0..STATE_ONLY_POSEIDON_TRACE_ROWS).find(|r| active[*r]).unwrap();
                        padding[row] = pv_rw_a_random_qm31();
                    }
                    2 => padding[dependent] = padding[dependent].add(QM31::from_cm31(CM31::from_m31(M31(1)))),
                    3 => {
                        padding.pop();
                    }
                    4 => h1.push(QM31::ZERO),
                    5 => {
                        let row = (0..STATE_ONLY_POSEIDON_TRACE_ROWS).rev().find(|r| active[*r]).unwrap();
                        padding[row] = pv_rw_a_random_qm31();
                        padding[dependent] = padding[dependent].add(QM31::from_cm31(CM31::from_m31(M31(1))));
                    }
                    6 => padding.push(QM31::ZERO),
                    _ => h1.clear(),
                }
                let mut h1_pin = h1.clone();
                let result = apply_h1_padding_mask_for_active(&mut h1, &padding, &active);
                let result_pin = apply_h1_padding_mask_for_active_pin(&mut h1_pin, &padding, &active);
                assert_eq!(result, result_pin, "case {case}");
                assert_eq!(h1, h1_pin, "case {case}");
                assert_eq!(result.is_ok(), case == 0);
            }
        }
    }

    /// pv-aspis-rw: the rewritten `balance_m31_copy_inactive` against the pin
    /// body: every layout's active rows and random ones, random tables, every
    /// kind of dependent row (inactive, active, first, last), and tables of
    /// the wrong length. Results and the written tables must be equal.
    #[test]
    fn pv_aspis_rw_balance_m31_matches_pin_body() {
        let mut actives: Vec<[bool; STATE_ONLY_POSEIDON_TRACE_ROWS]> =
            pv_rw_a_layouts().into_iter().map(|(_, active)| active).collect();
        for _ in 0..8 {
            let bytes: [u8; STATE_ONLY_POSEIDON_TRACE_ROWS] = pv_rw_a_random_bytes();
            actives.push(core::array::from_fn(|row| bytes[row] & 3 == 0));
        }
        actives.push([false; STATE_ONLY_POSEIDON_TRACE_ROWS]);
        let (mut ok, mut err) = (0usize, 0usize);
        for active in &actives {
            for case in 0..40usize {
                let length = match case % 10 {
                    7 => STATE_ONLY_POSEIDON_TRACE_ROWS - 1,
                    8 => STATE_ONLY_POSEIDON_TRACE_ROWS + 1,
                    9 => 0,
                    _ => STATE_ONLY_POSEIDON_TRACE_ROWS,
                };
                let mut table: Vec<M31> = (0..length)
                    .map(|_| M31(u32::from_le_bytes(pv_rw_a_random_bytes::<4>()) % P))
                    .collect();
                // Field edge values in a few rows.
                for (slot, value) in [0u32, 1, P - 1, P - 2].into_iter().enumerate() {
                    if slot * 97 < table.len() && case % 3 == 0 {
                        table[slot * 97] = M31(value);
                    }
                }
                let dependent = match case % 5 {
                    0 => 0,
                    1 => STATE_ONLY_POSEIDON_TRACE_ROWS - 1,
                    2 => first_inactive_row(active),
                    _ => usize::from(u16::from_le_bytes(pv_rw_a_random_bytes::<2>()))
                        % STATE_ONLY_POSEIDON_TRACE_ROWS,
                };
                let mut table_pin = table.clone();
                let result = balance_m31_copy_inactive(&mut table, dependent, active);
                let result_pin = balance_m31_copy_inactive_pin(&mut table_pin, dependent, active);
                assert_eq!(result, result_pin, "case {case}");
                assert_eq!(table, table_pin, "case {case}");
                if result.is_ok() {
                    ok += 1
                } else {
                    err += 1
                }
            }
        }
        assert!(ok > 50 && err > 50, "{ok} {err}");
    }

    fn pv_rw_a_assert_material_eq(a: &StateOnlyMaskMaterial, b: &StateOnlyMaskMaterial) {
        assert_eq!(a.c1, b.c1);
        assert_eq!(a.mask_only_c1, b.mask_only_c1);
        assert_eq!(a.g, b.g);
        assert_eq!(a.h1_padding, b.h1_padding);
        assert_eq!(a.mask_nonce, b.mask_nonce);
    }

    #[test]
    fn pv_rw_a_mask_material_build_and_apply_match_pin_bodies() {
        let hashes: [HashFn; 3] = [HOST_HASH, pv_rw_a_partly_rejecting_hash, pv_rw_a_rejecting_hash];
        for (layout, (cells, active)) in pv_rw_a_layouts().into_iter().enumerate() {
            for (hash_index, hash) in hashes.into_iter().enumerate() {
                for _ in 0..3 {
                    let entropy: [u8; 32] = pv_rw_a_random_bytes();
                    let nonce: [u8; 32] = pv_rw_a_random_bytes();
                    let binding: [u8; 32] = pv_rw_a_random_bytes();
                    let context = StateOnlyHidingContext::pinned([0x51; 32], nonce);
                    let mut store = InMemoryStateOnlyMaskNonceStore::default();
                    let mut store_pin = InMemoryStateOnlyMaskNonceStore::default();
                    let built = build_mask_material_for_layout(
                        hash, binding, context, &entropy, &mut store, &cells, &active,
                    );
                    let built_pin = build_mask_material_for_layout_pin(
                        hash, binding, context, &entropy, &mut store_pin, &cells, &active,
                    );
                    // A reused nonce is rejected identically.
                    assert_eq!(
                        build_mask_material_for_layout(
                            hash, binding, context, &entropy, &mut store, &cells, &active,
                        )
                        .err(),
                        build_mask_material_for_layout_pin(
                            hash, binding, context, &entropy, &mut store_pin, &cells, &active,
                        )
                        .err(),
                    );
                    let (material, material_pin) = match (built, built_pin) {
                        (Ok(a), Ok(b)) => (a, b),
                        (a, b) => {
                            assert_eq!(a.err(), b.err());
                            assert_eq!(hash_index, 2);
                            continue;
                        }
                    };
                    pv_rw_a_assert_material_eq(&material, &material_pin);
                    let mut trace = zero_trace();
                    for column in trace.c1.iter_mut() {
                        for value in column.iter_mut() {
                            *value = M31(u32::from_le_bytes(pv_rw_a_random_bytes::<4>()) % P);
                        }
                    }
                    let mut trace_pin = zero_trace();
                    trace_pin.c1.clone_from(&trace.c1);
                    let applied = apply_mask_material_for_layout(&mut trace, material, &cells, &active);
                    let applied_pin =
                        apply_mask_material_for_layout_pin(&mut trace_pin, material_pin, &cells, &active);
                    assert_eq!(applied, applied_pin, "layout {layout}");
                    assert_eq!(trace.c1, trace_pin.c1, "layout {layout}");
                }
            }
            // Shape errors are reported identically.
            let entropy: [u8; 32] = pv_rw_a_random_bytes();
            let context = StateOnlyHidingContext::pinned([0x51; 32], pv_rw_a_random_bytes());
            let mut store = InMemoryStateOnlyMaskNonceStore::default();
            let mut store_pin = InMemoryStateOnlyMaskNonceStore::default();
            let mut material =
                build_mask_material_for_layout(HOST_HASH, [1; 32], context, &entropy, &mut store, &cells, &active)
                    .unwrap();
            let mut material_pin = build_mask_material_for_layout_pin(
                HOST_HASH, [1; 32], context, &entropy, &mut store_pin, &cells, &active,
            )
            .unwrap();
            material.g.pop();
            material_pin.g.pop();
            let mut trace = zero_trace();
            let mut trace_pin = zero_trace();
            assert_eq!(
                apply_mask_material_for_layout(&mut trace, material, &cells, &active),
                apply_mask_material_for_layout_pin(&mut trace_pin, material_pin, &cells, &active),
            );
        }
    }

    fn inactive_m31_sum(table: &[M31], active: &[bool; 1024]) -> M31 {
        table
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
    }

    #[test]
    fn pool_material_and_h1_helpers_use_the_exact_variant_contexts() {
        let transfer_context =
            StateOnlyHidingContext::pool_v1_private_transfer([0x73; 32], [0x41; 32]);
        let (transfer_binding, _) = precommit(transfer_context);
        let mut transfer_store = InMemoryStateOnlyMaskNonceStore::default();
        let transfer_material = build_pool_v1_private_transfer_mask_material_v1(
            HOST_HASH,
            transfer_binding,
            transfer_context,
            [0x31; 32],
            &mut transfer_store,
        )
        .unwrap();
        assert_eq!(transfer_material.c1.len(), 5_428);
        let mut transfer_trace = zero_trace();
        let transfer_applied =
            apply_pool_v1_private_transfer_mask_material_v1(&mut transfer_trace, transfer_material)
                .unwrap();
        let transfer_active = pool_v1_private_transfer_copy_active_rows();
        assert!(transfer_trace
            .c1
            .iter()
            .all(|column| inactive_m31_sum(column, &transfer_active) == M31::ZERO));
        let mut transfer_h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_pool_v1_private_transfer_h1_padding_mask_v1(
            &mut transfer_h1,
            &transfer_applied.h1_padding,
        )
        .unwrap();
        assert_eq!(transfer_h1, transfer_applied.h1_padding);

        let withdrawal_context = StateOnlyHidingContext::pool_v1_withdrawal([0x73; 32], [0x42; 32]);
        let (withdrawal_binding, _) = precommit(withdrawal_context);
        let mut withdrawal_store = InMemoryStateOnlyMaskNonceStore::default();
        let withdrawal_material = build_pool_v1_withdrawal_mask_material_v1(
            HOST_HASH,
            withdrawal_binding,
            withdrawal_context,
            [0x32; 32],
            &mut withdrawal_store,
        )
        .unwrap();
        assert_eq!(withdrawal_material.c1.len(), 5_428);
        let mut withdrawal_trace = zero_trace();
        let withdrawal_applied =
            apply_pool_v1_withdrawal_mask_material_v1(&mut withdrawal_trace, withdrawal_material)
                .unwrap();
        let withdrawal_active = pool_v1_withdrawal_copy_active_rows();
        assert!(withdrawal_trace
            .c1
            .iter()
            .all(|column| inactive_m31_sum(column, &withdrawal_active) == M31::ZERO));
        let mut withdrawal_h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_pool_v1_withdrawal_h1_padding_mask_v1(
            &mut withdrawal_h1,
            &withdrawal_applied.h1_padding,
        )
        .unwrap();
        assert_eq!(withdrawal_h1, withdrawal_applied.h1_padding);

        let mut wrong_store = InMemoryStateOnlyMaskNonceStore::default();
        assert_eq!(
            build_pool_v1_private_transfer_mask_material_v1(
                HOST_HASH,
                withdrawal_binding,
                withdrawal_context,
                [0x33; 32],
                &mut wrong_store,
            )
            .err(),
            Some(StateOnlyMaskBuildError::Layout),
        );
    }

    #[test]
    fn pair_forest_material_uses_exact_ranked_layout_and_copy_registry() {
        let context = StateOnlyHidingContext::pool_v1_pair_forest_v1([0x73; 32], [0x48; 32]);
        let (binding, _) = precommit(context);
        let mut store = InMemoryStateOnlyMaskNonceStore::default();
        let material = build_pool_v1_pair_forest_mask_material_v1(
            HOST_HASH, binding, context, [0x38; 32], &mut store,
        )
        .unwrap();
        assert_eq!(material.c1.len(), 3_803);

        let mut trace = zero_trace();
        let applied = apply_pool_v1_pair_forest_mask_material_v1(&mut trace, material).unwrap();
        let active = pool_v1_pair_forest_copy_active_rows().unwrap();
        assert!(trace
            .c1
            .iter()
            .all(|column| inactive_m31_sum(column, &active) == M31::ZERO));
        let mut h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h1, &applied.h1_padding).unwrap();
        assert_eq!(h1, applied.h1_padding);

        let mut wrong_store = InMemoryStateOnlyMaskNonceStore::default();
        assert_eq!(
            build_pool_v1_pair_forest_mask_material_v1(
                HOST_HASH,
                binding,
                StateOnlyHidingContext::pool_v1_private_transfer([0x73; 32], [0x49; 32]),
                [0x39; 32],
                &mut wrong_store,
            )
            .err(),
            Some(StateOnlyMaskBuildError::Layout)
        );
    }

    #[test]
    fn private_seed_material_is_exact_fresh_and_consumed_once() {
        let context = mask_context(0xa7);
        let (binding, _) = precommit(context);
        let mut first_store = InMemoryStateOnlyMaskNonceStore::default();
        let material = build_state_only_mask_material(
            HOST_HASH,
            binding,
            context,
            [0x31; 32],
            &mut first_store,
        )
        .unwrap();
        assert_eq!(material.c1.len(), 5_374);
        assert!(material
            .mask_only_c1
            .iter()
            .all(|column| column.len() == STATE_ONLY_POSEIDON_TRACE_ROWS));
        assert_eq!(material.g.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        assert_eq!(material.h1_padding.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        let expected_c1 = material.c1.clone();
        let expected_mask_only_c1 = material.mask_only_c1.clone();
        let expected_g = material.g.clone();
        let expected_h1_padding = material.h1_padding.clone();
        assert!(expected_mask_only_c1
            .iter()
            .all(|column| state_only_copy_inactive_sum_m31(column) == Some(M31::ZERO)));
        assert_eq!(
            state_only_copy_inactive_sum_qm31(&expected_g),
            Some(QM31::ZERO)
        );
        assert_eq!(
            state_only_copy_inactive_sum_qm31(&expected_h1_padding),
            Some(QM31::ZERO)
        );
        assert!(state_only_copy_active_rows_v4()
            .iter()
            .all(|row| expected_h1_padding[usize::from(*row)] == QM31::ZERO));
        assert_eq!(
            STATE_ONLY_POSEIDON_TRACE_ROWS - state_only_copy_active_rows_v4().len() - 1,
            STATE_ONLY_H1_PADDING_MASK_FREE_QM31
        );

        assert_eq!(
            build_state_only_mask_material(
                HOST_HASH,
                binding,
                context,
                [0x41; 32],
                &mut first_store,
            )
            .err(),
            Some(StateOnlyMaskBuildError::ReusedMaskNonce)
        );

        let mut deterministic_store = InMemoryStateOnlyMaskNonceStore::default();
        let deterministic = build_state_only_mask_material(
            HOST_HASH,
            binding,
            context,
            [0x31; 32],
            &mut deterministic_store,
        )
        .unwrap();
        assert_eq!(deterministic.c1, expected_c1);
        assert_eq!(deterministic.mask_only_c1, expected_mask_only_c1);
        assert_eq!(deterministic.g, expected_g);
        assert_eq!(deterministic.h1_padding, expected_h1_padding);

        let fresh_context = mask_context(0xb3);
        let (fresh_binding, _) = precommit(fresh_context);
        let mut fresh_store = InMemoryStateOnlyMaskNonceStore::default();
        let fresh = build_state_only_mask_material(
            HOST_HASH,
            fresh_binding,
            fresh_context,
            [0x32; 32],
            &mut fresh_store,
        )
        .unwrap();
        assert_ne!(fresh.c1, expected_c1);
        assert_ne!(fresh.mask_only_c1, expected_mask_only_c1);
        assert_ne!(fresh.g, expected_g);
        assert_ne!(fresh.h1_padding, expected_h1_padding);

        let mut trace = zero_trace();
        let applied = apply_state_only_mask_material(&mut trace, material).unwrap();
        assert_eq!(applied.mask_only_c1, expected_mask_only_c1);
        assert_eq!(applied.g, expected_g);
        assert_eq!(applied.h1_padding, expected_h1_padding);
        let cells = state_only_relation_free_mask_cells_v4().unwrap();
        let active = copy_active_rows();
        let mut dependent = [None; STATE_ONLY_HIDING_C1_COLUMNS];
        for cell in &cells {
            let row = usize::from(cell.row);
            if !active[row] {
                dependent[usize::from(cell.column)] = Some(row);
            }
        }
        for (cell, expected) in cells.into_iter().zip(expected_c1) {
            let row = usize::from(cell.row);
            if dependent[usize::from(cell.column)] == Some(row) {
                continue;
            }
            assert_eq!(
                trace.c1[usize::from(cell.column)][usize::from(cell.row)],
                expected
            );
        }
        assert!(trace
            .c1
            .iter()
            .all(|column| state_only_copy_inactive_sum_m31(column) == Some(M31::ZERO)));
        let mut h1 = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        apply_state_only_h1_padding_mask(&mut h1, &applied.h1_padding).unwrap();
        assert_eq!(h1, applied.h1_padding);
        assert_eq!(state_only_copy_inactive_sum_qm31(&h1), Some(QM31::ZERO));
        assert_eq!(trace.c1[0][0], M31::ZERO);
    }

    #[test]
    fn zero_entropy_and_missing_root_binding_fail_closed() {
        let context = mask_context(0xc1);
        let (binding, mut transcript) = precommit(context);
        let mut store = InMemoryStateOnlyMaskNonceStore::default();
        assert_eq!(
            build_state_only_mask_material(HOST_HASH, binding, context, [0; 32], &mut store).err(),
            Some(StateOnlyMaskBuildError::ZeroPrivateEntropy)
        );

        let trace = zero_trace();
        let mask_only_c1 =
            core::array::from_fn(|_| vec![M31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS]);
        let g = vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS];
        assert_eq!(
            prove_masked_state_only_zerocheck(
                &mut transcript,
                binding,
                &trace,
                &mask_only_c1,
                &g,
                |_| Ok::<_, ()>(QM31::ZERO),
            ),
            Err(MaskedStateOnlyZerocheckError::RootsNotBound)
        );
    }

    fn snapshot(seed: u8) -> PublicAccountSnapshot {
        PublicAccountSnapshot {
            key: [seed; 32],
            owner: [seed.wrapping_add(1); 32],
            lamports: u64::from(seed) * 1_003,
            executable: seed & 1 == 1,
            rent_epoch: u64::from(seed) * 17,
            data: vec![seed; usize::from(seed % 7 + 1)],
        }
    }

    fn view() -> StateOnlyCompletePublicView {
        StateOnlyCompletePublicView {
            proof_bytes: (0..96u8).collect(),
            roots: vec![[0x11; 32], [0x22; 32]],
            openings: vec![vec![0x31; 64], vec![0x41; 16]],
            statement_values: vec![[0x51; 16], [0x61; 16]],
            program_logs: vec![b"verify-start".to_vec(), b"verify-ok".to_vec()],
            state_delta: PublicAccountDelta {
                before: Some(snapshot(1)),
                after: Some(snapshot(2)),
            },
            nullifier_delta: PublicAccountDelta {
                before: None,
                after: Some(snapshot(3)),
            },
            output_delta: PublicAccountDelta {
                before: None,
                after: Some(snapshot(4)),
            },
        }
    }

    #[test]
    fn complete_public_view_digest_has_per_category_and_position_teeth() {
        let baseline = view();
        let digest = baseline.digest(HOST_HASH);
        let encoded = baseline.canonical_bytes();
        for position in 0..encoded.len() {
            let mut mutated = encoded.clone();
            mutated[position] ^= 1;
            assert_ne!(
                HOST_HASH(&[VIEW_DOMAIN, &mutated]),
                digest,
                "position={position}"
            );
        }

        let mut proof = baseline.clone();
        proof.proof_bytes[0] ^= 1;
        assert_ne!(proof.digest(HOST_HASH), digest);
        let mut root = baseline.clone();
        root.roots[0][0] ^= 1;
        assert_ne!(root.digest(HOST_HASH), digest);
        let mut opening = baseline.clone();
        opening.openings[0][0] ^= 1;
        assert_ne!(opening.digest(HOST_HASH), digest);
        let mut statement = baseline.clone();
        statement.statement_values[0][0] ^= 1;
        assert_ne!(statement.digest(HOST_HASH), digest);
        let mut log = baseline.clone();
        log.program_logs[0][0] ^= 1;
        assert_ne!(log.digest(HOST_HASH), digest);
        let mut state = baseline.clone();
        state.state_delta.after.as_mut().unwrap().data[0] ^= 1;
        assert_ne!(state.digest(HOST_HASH), digest);
        let mut nullifier = baseline.clone();
        nullifier.nullifier_delta.after.as_mut().unwrap().lamports ^= 1;
        assert_ne!(nullifier.digest(HOST_HASH), digest);
        let mut output = baseline;
        output.output_delta.after.as_mut().unwrap().owner[0] ^= 1;
        assert_ne!(output.digest(HOST_HASH), digest);
    }
}

#[cfg(feature = "r0")]
pub mod r0 {
    use aspis_core::field::{WideExact, CM31, M31, QM31};
    use aspis_core::state_only_prefix::r0::{self as wire, Error, SemanticTranscript};
    use aspis_core::state_only_sumcheck::{
        evaluate_state_only_polynomial, state_only_boundary_sum,
    };

    /// R0 keeps all 28 coefficients on the wire, embedded in E. This is the
    /// same interpolation used by the legacy prover, with a new row driver.
    fn interpolate(values: &[QM31; 28]) -> [QM31; 28] {
        let mut out = [QM31::ZERO; 28];
        for i in 0..28 {
            let mut basis = [M31::ZERO; 28];
            basis[0] = M31::ONE;
            let mut degree = 0;
            let mut denominator = M31::ONE;
            for j in 0..28 {
                if i == j {
                    continue;
                }
                for k in (0..=degree + 1).rev() {
                    let shifted = if k == 0 { M31::ZERO } else { basis[k - 1] };
                    basis[k] = shifted.sub(basis[k].mul(M31(j as u32)));
                }
                degree += 1;
                denominator = denominator.mul(M31(i as u32).sub(M31(j as u32)));
            }
            let scale = values[i].mul_m31(denominator.inv());
            for k in 0..28 {
                out[k] = out[k].add(scale.mul_m31(basis[k]));
            }
        }
        out
    }

    pub fn prove_sumcheck(
        transcript: &mut SemanticTranscript,
        output: &mut Vec<u8>,
        initial_claim: QM31,
        mut oracle: impl FnMut(&[QM31; 10]) -> Result<QM31, Error>,
    ) -> Result<([QM31; 10], QM31), Error> {
        let mut point = [QM31::ZERO; 10];
        let mut running = initial_claim;
        for round in 0..10 {
            let remaining = 9 - round;
            let mut values = [QM31::ZERO; 28];
            for (sample, value) in values.iter_mut().enumerate() {
                point[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
                for assignment in 0..1usize << remaining {
                    for offset in 0..remaining {
                        point[round + 1 + offset] =
                            if (assignment >> (remaining - 1 - offset)) & 1 == 0 {
                                QM31::ZERO
                            } else {
                                QM31::ONE
                            };
                    }
                    *value = value.add(oracle(&point)?);
                }
            }
            let polynomial = interpolate(&values);
            if state_only_boundary_sum(&polynomial) != running {
                return Err(Error::Boundary { round });
            }
            let framed = wire::record(
                15 + round as u8,
                &wire::encode_values(polynomial.map(WideExact::from_qm31)),
            )?;
            point[round] = transcript.semantic(15 + round as u8, &framed)?;
            output.extend_from_slice(&framed);
            running = evaluate_state_only_polynomial(&polynomial, point[round]);
        }
        if oracle(&point)? != running {
            return Err(Error::Terminal);
        }
        Ok((point, running))
    }
}

fn state_only_mask_expander_block(hash: HashFn, seed: [u8;32], counter: u64) -> [u8;32] {
    hash(&[MASK_EXPAND_DOMAIN, &seed, &counter.to_le_bytes()])
}

#[cfg(kani)]
mod prover_commit_rom {
    use super::*;
    use crate::prover_commit_oracle as rom;

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn mask_block() {
        rom::reset(2);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        let actual = state_only_mask_expander_block(crate::HOST_HASH, seed, counter);
        let expected = crate::HOST_HASH(&[
            b"aspis:state-only:private-mask-expand:v1", &seed, &counter.to_le_bytes(),
        ]);
        assert_eq!(actual, expected);
    }

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn mask_next_word() {
        rom::reset(2);
        let seed = kani::any();
        let counter: u64 = kani::any();
        let block: [u8; 32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let mut actual = SeedExpander { hash: crate::HOST_HASH, seed, counter, block, word };
        let (expected_block, expected_counter, slot) = if word == 8 {
            (crate::HOST_HASH(&[b"aspis:state-only:private-mask-expand:v1", &seed, &counter.to_le_bytes()]), counter.wrapping_add(1), 0)
        } else { (block, counter, word) };
        let offset = 4 * slot;
        let expected = u32::from_le_bytes([
            expected_block[offset], expected_block[offset+1],
            expected_block[offset+2], expected_block[offset+3],
        ]);
        assert_eq!(actual.next_word(), expected);
        assert_eq!(actual.block, expected_block);
        assert_eq!(actual.counter, expected_counter);
        assert_eq!(actual.word, slot + 1);
        assert_eq!(actual.seed, seed);
    }
    // Exact m31 try body, with its return carried as an absorbing result.
    // The source m31 body is pinned and checked by harness/check-step-source.py.
    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn mask_try_step() {
        rom::reset(2);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8; 32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let successful: bool = kani::any();
        let value: u32 = kani::any();
        kani::assume(value < aspis_core::field::P);
        let result = if successful { Ok(aspis_core::field::M31(value)) }
            else { Err(StateOnlyMaskBuildError::MaskSampleExhausted) };
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::try_step(
            crate::HOST_HASH, b"aspis:state-only:private-mask-expand:v1", state, result);
        let mut actual = SeedExpander { hash: crate::HOST_HASH, seed: seed, counter, block, word };
        let observed = match result {
            Ok(value) => Ok(value),
            Err(_) => {
                let candidate = actual.next_word() & 0x7fff_ffff;
                if candidate < aspis_core::field::P {
                    Ok(aspis_core::field::M31(candidate))
                } else { Err(StateOnlyMaskBuildError::MaskSampleExhausted) }
            }
        };
        assert_eq!(observed, expected);
        assert_eq!(actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
        assert!(actual.word <= 8);
    }

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn mask_limb() {
        // At most three fresh blocks per side from any valid word slot.
        rom::reset(6);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8; 32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::limb(crate::HOST_HASH, b"aspis:state-only:private-mask-expand:v1", state);
        let mut actual = SeedExpander { hash: crate::HOST_HASH, seed: seed, counter, block, word };
        assert_eq!(actual.m31(), expected);
        assert_eq!(actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
    }

}

#[cfg(kani)]
mod prover_commit_caller7 {
    use super::*;
    use crate::prover_commit_oracle as rom;
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified(SeedExpander::next_word)]
    fn mask_limb_caller() {
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        rom::reset_expander(b"aspis:state-only:private-mask-expand:v1", seed, counter);
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::limb_caller(
            crate::HOST_HASH, b"aspis:state-only:private-mask-expand:v1", state);
        let mut actual = SeedExpander { hash: crate::HOST_HASH, seed: seed, counter, block, word };
        assert_eq!(actual.m31(), expected);
        assert_eq!(*&actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
    }
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified(rom::expander_query)]
    fn mask_qm31_caller() {
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        rom::reset_expander(b"aspis:state-only:private-mask-expand:v1", seed, counter);
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::qm31_caller(
            crate::HOST_HASH, b"aspis:state-only:private-mask-expand:v1", state);
        let mut actual = SeedExpander { hash: crate::HOST_HASH, seed: seed, counter, block, word };
        assert_eq!(actual.qm31(), expected);
        assert_eq!(*&actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
    }
    #[kani::proof_for_contract(SeedExpander::next_word)]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    fn mask_next_contract() {
        let seed: [u8;32] = kani::any();
        let base_counter: u64 = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        kani::assume(word < 8 || counter.wrapping_sub(base_counter) < 9);
        rom::reset_expander(b"aspis:state-only:private-mask-expand:v1", seed, base_counter);
        let mut actual = SeedExpander { hash: crate::HOST_HASH, seed: seed, counter, block, word };
        let _ = actual.next_word();
    }


}

#[cfg(kani)]
mod prover_commit_balance7 {
    use super::*;
    fn canonical(raw: u32) -> M31 {
        let value = raw & 0x7fff_ffff;
        M31(if value == P { 0 } else { value })
    }
    #[kani::proof]
    #[kani::unwind(1026)]
    fn balance_m31_caller() {
        let raw: [u32;1024] = kani::any();
        let table: Vec<M31> = raw.into_iter().map(canonical).collect();
        let mut active: [bool;1024] = kani::any();
        let dependent: usize = kani::any();
        let probe: usize = kani::any();
        kani::assume(dependent < 1024 && probe < 1024);
        active[dependent] = false;
        let mut actual = table.clone();
        let observed = balance_m31_copy_inactive(&mut actual, dependent, &active);
        let (expected, table) = crate::prover_commit_reference::balance_m31_owned(table, dependent, &active);
        assert_eq!(observed, expected);
        assert_eq!(actual.len(), table.len());
        assert_eq!(actual[probe].0, table[probe].0);
    }
    #[kani::proof]
    #[kani::unwind(4098)]
    fn balance_qm31_caller() {
        let raw: [u32;4096] = kani::any();
        let mut table = Vec::with_capacity(1024);
        for row in 0..1024 {
            table.push(QM31 { c0: CM31::new(canonical(raw[4*row]), canonical(raw[4*row+1])),
                c1: CM31::new(canonical(raw[4*row+2]), canonical(raw[4*row+3])) });
        }
        let mut active: [bool;1024] = kani::any();
        let dependent: usize = kani::any();
        let probe: usize = kani::any();
        kani::assume(dependent < 1024 && probe < 1024);
        active[dependent] = false;
        let mut actual = table.clone();
        let observed = balance_qm31_copy_inactive(&mut actual, dependent, &active);
        let (expected, table) = crate::prover_commit_reference::balance_qm31_owned(table, dependent, &active);
        assert_eq!(observed, expected);
        assert_eq!(actual.len(), table.len());
        assert_eq!(actual[probe].c0.a.0, table[probe].c0.a.0);
        assert_eq!(actual[probe].c0.b.0, table[probe].c0.b.0);
        assert_eq!(actual[probe].c1.a.0, table[probe].c1.a.0);
        assert_eq!(actual[probe].c1.b.0, table[probe].c1.b.0);
    }
}

/// Single-row comparisons, with arbitrary accumulated sum. These establish
/// the fold transition, not an extraction of the full iterator consumer.
#[cfg(kani)]
mod prover_commit_balance8 {
    use super::*;
    fn canonical(raw: u32) -> M31 {
        let v = raw & 0x7fff_ffff;
        M31(if v == P { 0 } else { v })
    }
    fn field() -> QM31 {
        QM31 { c0: CM31::new(canonical(kani::any()), canonical(kani::any())),
            c1: CM31::new(canonical(kani::any()), canonical(kani::any())) }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn m31_step() {
        let sum = canonical(kani::any());
        let value = canonical(kani::any());
        let active: bool = kani::any();
        let row: usize = kani::any();
        let dependent: usize = kani::any();
        let observed = core::iter::once(row)
            .filter(|r| !active && *r != dependent)
            .fold(sum, |s, _| s.add(value));
        let expected = crate::prover_commit_reference::balance_m31_step(sum, value, active, row, dependent);
        assert_eq!(observed, expected);
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn qm31_step() {
        let sum = field();
        let value = field();
        let active: bool = kani::any();
        let row: usize = kani::any();
        let dependent: usize = kani::any();
        let observed = core::iter::once(row)
            .filter(|r| !active && *r != dependent)
            .fold(sum, |s, _| s.add(value));
        let expected = crate::prover_commit_reference::balance_qm31_step(sum, value, active, row, dependent);
        assert_eq!(observed, expected);
    }
}

/// Universal four-call control-flow comparison over an arbitrary scalar trace.
/// Stubs are relational inputs, not asserted scalar contracts. Each side sees
/// the same trace; all sampled results and successor states are unconstrained.
#[cfg(kani)]
mod prover_commit_four8 {
    use super::*;
    use aspis_core::field::{M31, QM31};
    use crate::prover_commit_reference::State;
    type Sample = Result<M31, StateOnlyMaskBuildError>;
    const ZERO: State = State { seed: [0;32], counter: 0, block: [0;32], word: 0 };
    static mut STATES: [State;4] = [ZERO;4];
    static mut VALUES: [Sample;4] = [Ok(M31::ZERO);4];
    static mut CURSOR: usize = 0;
    fn transition() -> (Sample, State) {
        unsafe {
            assert!(CURSOR < 4);
            let pair = (VALUES[CURSOR], STATES[CURSOR]);
            CURSOR += 1;
            pair
        }
    }
    fn shipped_scalar(state: &mut SeedExpander) -> Sample {
        let (value, after) = transition();
        state.seed = after.seed;
        state.counter = after.counter;
        state.block = after.block;
        state.word = after.word;
        value
    }
    fn reference_scalar(_: aspis_core::HashFn, _: &[u8], _: State) -> (Sample, State) {
        transition()
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(SeedExpander::m31, shipped_scalar)]
    #[kani::stub(crate::prover_commit_reference::limb_caller, reference_scalar)]
    fn four_control() {
        for i in 0..4 {
            unsafe {
                STATES[i] = kani::any();
                VALUES[i] = if kani::any::<bool>() { Ok(M31(kani::any())) }
                    else { Err(StateOnlyMaskBuildError::MaskSampleExhausted) };
            }
        }
        let state: State = kani::any();
        unsafe { CURSOR = 0; }
        let (expected, after) = crate::prover_commit_reference::qm31_caller(
            crate::HOST_HASH, b"unused relational input", state);
        let expected_calls = unsafe { CURSOR };
        unsafe { CURSOR = 0; }
        let mut actual = SeedExpander { hash: crate::HOST_HASH,
            seed: state.seed, counter: state.counter, block: state.block, word: state.word };
        let observed: Result<QM31, StateOnlyMaskBuildError> = actual.qm31();
        assert_eq!(observed, expected);
        assert_eq!(actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
        assert_eq!(unsafe { CURSOR }, expected_calls);
    }
}

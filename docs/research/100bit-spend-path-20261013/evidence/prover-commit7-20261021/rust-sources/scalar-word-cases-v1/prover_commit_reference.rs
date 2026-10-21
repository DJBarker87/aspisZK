//! Owned, proof-only expander reference for Kani/Aeneas. No SHA algorithm.
use aspis_core::{HashFn, field::{M31, P}};
use crate::state_only_hiding::StateOnlyMaskBuildError;

#[derive(Clone, Copy)]
#[cfg_attr(kani, derive(kani::Arbitrary, PartialEq, Eq))]
pub(crate) struct State {
    pub(crate) seed: [u8; 32],
    pub(crate) counter: u64,
    pub(crate) block: [u8; 32],
    pub(crate) word: usize,
}

#[cfg_attr(kani, kani::requires(hash == crate::HOST_HASH))]
#[cfg_attr(kani, kani::requires(state.word <= 8))]
#[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::known_domain(domain)))]
#[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::expander_domain(domain, state.seed, state.counter, state.word)))]
#[cfg_attr(kani, kani::ensures(|result| *result == pure_next(old(state))))]
pub(crate) fn next(hash: HashFn, domain: &[u8], mut state: State) -> (u32, State) {
    if state.word == 8 {
        state.block = hash(&[domain, &state.seed, &state.counter.to_le_bytes()]);
        state.counter = state.counter.wrapping_add(1);
        state.word = 0;
    }
    let offset = state.word * 4;
    let bytes = [state.block[offset], state.block[offset+1], state.block[offset+2], state.block[offset+3]];
    state.word += 1;
    (u32::from_le_bytes(bytes), state)
}

pub(crate) fn limb(hash: HashFn, domain: &[u8], mut state: State)
    -> (Result<M31, StateOnlyMaskBuildError>, State)
{
    let mut attempts = 0;
    let mut result = Err(StateOnlyMaskBuildError::MaskSampleExhausted);
    while attempts < 16 {
        result = match result {
            Ok(value) => Ok(value),
            Err(error) => {
                let (word, after) = next(hash, domain, state);
                state = after;
                let candidate = word & 0x7fff_ffff;
                if candidate < P { Ok(M31(candidate)) } else { Err(error) }
            }
        };
        attempts += 1;
    }
    (result, state)
}

/// One carried-result transition. Success is absorbing, including its state.
#[cfg(kani)]
pub(crate) fn try_step(hash: HashFn, domain: &[u8], state: State,
    result: Result<M31, StateOnlyMaskBuildError>)
    -> (Result<M31, StateOnlyMaskBuildError>, State)
{
    match result {
        Ok(value) => (Ok(value), state),
        Err(error) => {
            let (word, after) = next(hash, domain, state);
            let candidate = word & 0x7fff_ffff;
            (if candidate < P { Ok(M31(candidate)) } else { Err(error) }, after)
        }
    }
}

/// Same early-return control flow as the shipped scalar callers. This avoids
/// comparing a short-circuit loop with the carried-result normal form.
#[cfg(any(kani, aeneas_ref))]
#[cfg_attr(kani, kani::requires(hash == crate::HOST_HASH))]
#[cfg_attr(kani, kani::requires(state.word <= 8))]
#[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::known_domain(domain)))]
#[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::scalar_domain(domain, state.seed, state.counter)))]
#[cfg_attr(kani, kani::ensures(|result| *result == pure_scalar(old(state))))]
pub(crate) fn limb_caller(hash: HashFn, domain: &[u8], mut state: State)
    -> (Result<M31, StateOnlyMaskBuildError>, State)
{
    for _ in 0..16 {
        let (word, after) = next(hash, domain, state);
        state = after;
        let candidate = word & 0x7fff_ffff;
        if candidate < P { return (Ok(M31(candidate)), state); }
    }
    (Err(StateOnlyMaskBuildError::MaskSampleExhausted), state)
}

#[cfg(kani)]
pub(crate) fn next_matches(domain: &[u8], before: State, value: u32, after: State) -> bool {
    let (expected, state) = next(crate::HOST_HASH, domain, before);
    value == expected && after.seed == state.seed && after.counter == state.counter &&
        after.block == state.block && after.word == state.word
}

/// Four scalar calls in Rust's left-to-right tower coordinate order.
#[cfg(any(kani, aeneas_ref))]
pub(crate) fn qm31_caller(hash: HashFn, domain: &[u8], state: State)
    -> (Result<aspis_core::field::QM31, StateOnlyMaskBuildError>, State)
{
    let (a, state) = limb_caller(hash, domain, state);
    let a = match a { Ok(v) => v, Err(e) => return (Err(e), state) };
    let (b, state) = limb_caller(hash, domain, state);
    let b = match b { Ok(v) => v, Err(e) => return (Err(e), state) };
    let (c, state) = limb_caller(hash, domain, state);
    let c = match c { Ok(v) => v, Err(e) => return (Err(e), state) };
    let (d, state) = limb_caller(hash, domain, state);
    let d = match d { Ok(v) => v, Err(e) => return (Err(e), state) };
    (Ok(aspis_core::field::QM31 { c0: aspis_core::field::CM31::new(a,b),
        c1: aspis_core::field::CM31::new(c,d) }), state)
}

/// Owned balancing references, with the same ascending row order and final
/// dependent-cell assignment as the shipped helpers. No iterator borrows
/// escape an iteration.
pub(crate) fn balance_m31_owned(mut table: Vec<M31>, dependent: usize,
    active: &[bool; 1024]) -> (Result<(), StateOnlyMaskBuildError>, Vec<M31>)
{
    if table.len() != 1024 || active[dependent] {
        return (Err(StateOnlyMaskBuildError::TraceShape), table);
    }
    let mut sum = M31::ZERO;
    for row in 0..1024usize {
        if !active[row] && row != dependent { sum = sum.add(table[row]); }
    }
    table[dependent] = M31::ZERO.sub(sum);
    (Ok(()), table)
}

pub(crate) fn balance_qm31_owned(mut table: Vec<aspis_core::field::QM31>, dependent: usize,
    active: &[bool; 1024]) -> (Result<(), StateOnlyMaskBuildError>, Vec<aspis_core::field::QM31>)
{
    if table.len() != 1024 || active[dependent] {
        return (Err(StateOnlyMaskBuildError::TraceShape), table);
    }
    let mut sum = aspis_core::field::QM31::ZERO;
    for row in 0..1024usize {
        if !active[row] && row != dependent { sum = sum.add(table[row]); }
    }
    table[dependent] = aspis_core::field::QM31::ZERO.sub(sum);
    (Ok(()), table)
}

/// Pure operational models used by verified summaries. Input framing is
/// checked once by each next-word contract, not repeated inside its summary.
#[cfg(kani)]
fn pure_next(mut state: State) -> (u32, State) {
    if state.word == 8 {
        state.block = crate::prover_commit_oracle::expander_block(state.counter);
        state.counter = state.counter.wrapping_add(1);
        state.word = 0;
    }
    let offset = 4 * state.word;
    let word = u32::from_le_bytes([state.block[offset], state.block[offset+1],
        state.block[offset+2], state.block[offset+3]]);
    state.word += 1;
    (word, state)
}
#[cfg(kani)]
fn pure_scalar(mut state: State) -> (Result<M31, StateOnlyMaskBuildError>, State) {
    for _ in 0..16 {
        let (word, after) = pure_next(state);
        state = after;
        let candidate = word & 0x7fff_ffff;
        if candidate < P { return (Ok(M31(candidate)), state); }
    }
    (Err(StateOnlyMaskBuildError::MaskSampleExhausted), state)
}
#[cfg(kani)]
pub(crate) fn limb_matches(domain: &[u8], before: State,
    value: Result<M31, StateOnlyMaskBuildError>, after: State) -> bool {
    let (expected, state) = limb_caller(crate::HOST_HASH, domain, before);
    value == expected && after == state
}
#[cfg(kani)]
mod contracts {
    use super::*;
    use crate::prover_commit_oracle as rom;
    fn domain() -> &'static [u8] {
        if kani::any::<bool>() { b"aspis:state-only:private-mask-expand:v1" }
        else { b"aspis:state-only:profile21:source-expand:v1" }
    }
    #[kani::proof_for_contract(next)]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    fn reference_next() {
        let domain = domain();
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let base: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        kani::assume(word < 8 || counter.wrapping_sub(base) < 9);
        rom::reset_expander(domain, seed, base);
        let _ = next(crate::HOST_HASH, domain, State { seed, counter, block, word });
    }
    #[kani::proof_for_contract(limb_caller)]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified(next)]
    fn reference_scalar() {
        let domain = domain();
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let base: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8 && counter.wrapping_sub(base) <= 6);
        rom::reset_expander(domain, seed, base);
        let _ = limb_caller(crate::HOST_HASH, domain, State { seed, counter, block, word });
    }
    // BEGIN PROVER_COMMIT7_SCALAR_WORD_CASES
    fn scalar_at(word: usize) {
        let domain = domain();
        let seed: [u8;32] = kani::any();
        let base: u64 = kani::any();
        let delta: u8 = kani::any();
        kani::assume(delta <= 6);
        let counter = base.wrapping_add(u64::from(delta));
        let block: [u8;32] = kani::any();
        rom::reset_expander(domain, seed, base);
        let _ = limb_caller(crate::HOST_HASH, domain, State { seed, counter, block, word });
    }
    macro_rules! scalar_word_case { ($name:ident, $word:expr) => {
    #[kani::proof_for_contract(limb_caller)]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified(next)]
    fn $name() { scalar_at($word); }
    }; }
    scalar_word_case!(reference_scalar_w0, 0);
    scalar_word_case!(reference_scalar_w1, 1);
    scalar_word_case!(reference_scalar_w2, 2);
    scalar_word_case!(reference_scalar_w3, 3);
    scalar_word_case!(reference_scalar_w4, 4);
    scalar_word_case!(reference_scalar_w5, 5);
    scalar_word_case!(reference_scalar_w6, 6);
    scalar_word_case!(reference_scalar_w7, 7);
    scalar_word_case!(reference_scalar_w8, 8);
    // END PROVER_COMMIT7_SCALAR_WORD_CASES

}

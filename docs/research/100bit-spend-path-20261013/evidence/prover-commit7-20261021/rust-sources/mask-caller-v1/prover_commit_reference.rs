//! Owned, proof-only expander reference for Kani/Aeneas. No SHA algorithm.
use aspis_core::{HashFn, field::{M31, P}};
use crate::state_only_hiding::StateOnlyMaskBuildError;

#[derive(Clone, Copy)]
pub(crate) struct State {
    pub(crate) seed: [u8; 32],
    pub(crate) counter: u64,
    pub(crate) block: [u8; 32],
    pub(crate) word: usize,
}

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

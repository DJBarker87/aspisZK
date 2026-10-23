#![cfg(kani)]
#![allow(non_snake_case)]
use aspis_statement::pool_v1::*;
use solana_program_error::ProgramError;
type ProgramResult = Result<(), ProgramError>;
mod statement;
// Explicit model of a reached returning runtime syscall. It changes only the
// return-data observation, once. Runtime/P6 binding is a retained premise.
mod program {
    pub static mut CALLS: usize = 0;
    pub static mut LEN: usize = 0;
    pub static mut INDEX: usize = 0;
    pub static mut BYTE: u8 = 0;
    pub fn set_return_data(bytes: &[u8]) {
        unsafe {
            CALLS += 1;
            LEN = bytes.len();
            assert!(INDEX < bytes.len());
            BYTE = bytes[INDEX];
        }
    }
}
include!("S2I_emit.rs");

#[kani::proof]
#[kani::unwind(70)]
fn S2I_emit_native() {
    let s = statement::statement();
    let i: usize = kani::any();
    kani::assume(i < POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES);
    unsafe { program::INDEX = i; }
    let reply = emit_result(&s);
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: s.transition_kind(),
        master_account: s.common().master_account,
        selected_lane_account: s.common().selected_lane_account,
        output_lane: s.common().output_lane,
        nullifier: *s.nullifier(),
        verified_afterstate: s.common().lane_transition.candidate_afterstate,
    };
    let validation = validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&s, &result);
    if validation.is_err() {
        assert_eq!(reply, Err(ProgramError::InvalidInstructionData));
        unsafe { assert_eq!(program::CALLS, 0); }
    } else {
        match encode_pool_v1_pair_forest_terminal_result_v1(&result) {
            Err(_) => {
                assert_eq!(reply, Err(ProgramError::InvalidInstructionData));
                unsafe { assert_eq!(program::CALLS, 0); }
            }
            Ok(bytes) => {
                assert_eq!(reply, Ok(()));
                assert_eq!(bytes.len(), 792);
                assert_eq!(&bytes[..4], b"ASR8");
                unsafe {
                    assert_eq!(program::CALLS, 1);
                    assert_eq!(program::LEN, 792);
                    assert_eq!(program::BYTE, bytes[i]);
                }
                kani::cover!(s.transition_kind() == PoolV1TransitionKind::PrivateTransfer);
                kani::cover!(s.transition_kind() == PoolV1TransitionKind::Withdrawal);
            }
        }
    }
}

#[kani::proof]
#[kani::unwind(70)]
fn S2I_result_encoder_header() {
    let s = statement::statement();
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: s.transition_kind(),
        master_account: s.common().master_account,
        selected_lane_account: s.common().selected_lane_account,
        output_lane: s.common().output_lane,
        nullifier: *s.nullifier(),
        verified_afterstate: s.common().lane_transition.candidate_afterstate,
    };
    if let Ok(bytes) = encode_pool_v1_pair_forest_terminal_result_v1(&result) {
        assert_eq!(bytes.len(), 792);
        assert_eq!(&bytes[..4], b"ASR8");
        assert_eq!(bytes[5], result.transition_kind as u8);
        assert_eq!(bytes[7], result.output_lane);
        kani::cover!(result.transition_kind == PoolV1TransitionKind::PrivateTransfer);
        kani::cover!(result.transition_kind == PoolV1TransitionKind::Withdrawal);
    }
}

// Isolated replacement for the failed whole-success gate: all other complete
// statement fields remain arbitrary. This is rejection-only evidence.
#[kani::proof]
#[kani::unwind(70)]
fn S2I_emit_zero_master_rejects() {
    let mut s = statement::statement();
    match &mut s {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, .. } |
        PoolV1PairForestTerminalStatementV1::Withdrawal { common, .. } => {
            common.master_account = [0;32];
        }
    }
    let reply = emit_result(&s);
    assert_eq!(reply, Err(ProgramError::InvalidInstructionData));
    unsafe { assert_eq!(program::CALLS, 0); }
    kani::cover!(s.transition_kind() == PoolV1TransitionKind::PrivateTransfer);
    kani::cover!(s.transition_kind() == PoolV1TransitionKind::Withdrawal);
}

// Second split: avoid constructing the 1880-byte input statement at all. The
// native result encoder is called on its direct792-byte domain instead.
#[kani::proof]
#[kani::unwind(34)]
fn S2I_direct_result_encoder_header() {
    use aspis_core::field::M31;
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: if kani::any() { PoolV1TransitionKind::PrivateTransfer } else { PoolV1TransitionKind::Withdrawal },
        master_account: core::array::from_fn(|_| kani::any()),
        selected_lane_account: core::array::from_fn(|_| kani::any()),
        output_lane: kani::any(),
        nullifier: core::array::from_fn(|_| M31(kani::any())),
        verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: kani::any(),
            next_root: core::array::from_fn(|_| M31(kani::any())),
            next_frontier: core::array::from_fn(|_| core::array::from_fn(|_| M31(kani::any()))),
        },
    };
    if let Ok(bytes) = encode_pool_v1_pair_forest_terminal_result_v1(&result) {
        assert_eq!(bytes.len(), 792);
        assert_eq!(&bytes[..4], b"ASR8");
        assert_eq!(bytes[5], result.transition_kind as u8);
        assert_eq!(bytes[7], result.output_lane);
        kani::cover!(result.transition_kind == PoolV1TransitionKind::PrivateTransfer);
        kani::cover!(result.transition_kind == PoolV1TransitionKind::Withdrawal);
    }
}

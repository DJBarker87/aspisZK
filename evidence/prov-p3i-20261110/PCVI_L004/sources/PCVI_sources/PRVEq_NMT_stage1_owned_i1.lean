-- PCVI_ item 3: NMT stage1_owned (second shape, order table). Fresh text: model-bridge-20261111/NND_reuse/NMT_fresh/.../stage1_owned/raw/NMT_stage1_owned/Funs.lean
-- (Aeneas emission of programs/r1-cost-probe, r1_pool_adapter_owned.rs). Each external callee is replaced by the gate's NMT_call_k parameter
-- in the order read off the gate body: 0 Slice ne, 1 Slice eq, 2 Result.map_err, 3 Variant.tag, 4 PROOF_BYTES, 5 semantic_public, 6 common,
-- 7 validate_..._statement_v1, 8 POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, 9 encode_..._afterstate_v1, 10 ProgramError clone, 11 first_decoded,
-- 12 decode_public_statement_box, 13 require_readonly_buffer, 14 require_verifier_checkpoint, 15 require_distinct_accounts, 16 require_zero.
-- Statement quantifies over all callees; which frozen items they are is the binding at the instantiation (CONDITIONAL_ON_BINDING).
import Aeneas
import NMT_stage1_owned.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace NMT_stage1_owned
namespace PRVFresh_i1
-- Opaque callees are explicit parameters, never axioms.
variable (NMT_call_0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NMT_call_1 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NMT_call_2 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
(core.result.Result T E) → O → Result (core.result.Result T F))

variable (NMT_call_3 : aspis_r1_cost_probe.transport.Variant → Result Std.U8)

variable (NMT_call_4 : Result Std.Usize)

variable (NMT_call_5 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)

variable (NMT_call_6 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)

variable (NMT_call_7 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result (core.result.Result Unit
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))

variable (NMT_call_8 : Result Std.Usize)

variable (NMT_call_9 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
    Result (core.result.Result (Array Std.U8 688#usize)
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1))

variable (NMT_call_10 : solana_program_error.ProgramError → Result
    solana_program_error.ProgramError)

variable (NMT_call_11 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → (Slice Std.U8) → Std.Usize → Result (core.result.Result
    (alloc.vec.Vec Std.U8) solana_program_error.ProgramError))

variable (NMT_call_12 : (Slice Std.U8) → Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    solana_program_error.ProgramError))

variable (NMT_call_13 : r1_pool_adapter.owned.OwnedAccount → Result (core.result.Result Unit
    solana_program_error.ProgramError))

variable (NMT_call_14 : r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → Bool →
    Result (core.result.Result Unit solana_program_error.ProgramError))

variable (NMT_call_15 : ∀ {N : Std.Usize},
(Array r1_pool_adapter.owned.OwnedAccount N) → Result (core.result.Result
    Unit solana_program_error.ProgramError))

variable (NMT_call_16 : (Slice Std.U8) → Result (core.result.Result Unit
    solana_program_error.ProgramError))

/-- OwnedAccount.data with the SDK clone callee as the parameter NMT_call_10 (as in the gate). -/
def r1_pool_adapter.owned.OwnedAccount.data (NMT_call_10 : solana_program_error.ProgramError → Result
    solana_program_error.ProgramError)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  := do
  match self.bytes with
  | core.result.Result.Ok bytes =>
    let s := alloc.vec.Vec.deref bytes
    ok (core.result.Result.Ok s)
  | core.result.Result.Err error =>
    let pe ← NMT_call_10 error
    ok (core.result.Result.Err pe)

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure#1}::call_once]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 396:13-396:49 -/
def
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage1_owned.closure_1)
  (tupled_args :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

/-- Trait implementation: [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure#1}]
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 396:13-396:49 -/
@[reducible]
def
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage1_owned.closure_1
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
}

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure}::call_once]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 392:17-392:53 -/
def
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage1_owned.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

/-- Trait implementation: [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure}]
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 392:17-392:53 -/
@[reducible]
def
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage1_owned.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
}

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 376:0-414:1 -/
def r1_pool_adapter.owned.stage1_owned
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ←
    NMT_call_1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  if b
  then
    let i := Slice.len accounts
    if i != 3#usize
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let proof_account ← Slice.index_usize accounts 0#usize
      let public_account ← Slice.index_usize accounts 1#usize
      let checkpoint_account ← Slice.index_usize accounts 2#usize
      let r ←
        NMT_call_15
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← NMT_call_13 proof_account
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ←
            NMT_call_13 public_account
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ←
              NMT_call_14
                checkpoint_account program_id true
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ←
                (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) checkpoint_account
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← NMT_call_16 val
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ←
                    (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) public_account
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← NMT_call_12 val1
                    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ←
                        NMT_call_7
                          val2
                      let r9 ←
                        NMT_call_2
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ←
                          NMT_call_6
                            val2
                        let r10 ←
                          NMT_call_9
                            pvpftcv.lane_transition.candidate_afterstate
                        let r11 ←
                          NMT_call_2
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ←
                            (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10)
                              proof_account
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ←
                              NMT_call_4
                            let proof_start ←
                              NMT_call_8
                            let o ←
                              lift (Usize.checked_add proof_start proof_length)
                            let r13 ←
                              core.option.Option.ok_or o
                                solana_program_error.ProgramError.InvalidAccountData
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let i1 := Slice.len val4
                              if i1 != val5
                              then
                                ok (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData)
                              else
                                let s ←
                                  core.slice.index.Slice.index
                                    (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8) val4 { «end» := proof_start }
                                let b1 ←
                                  NMT_call_0
                                    core.cmp.PartialEqU8 s val3
                                if b1
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ←
                                    lift (Std.Usize.wrapping_add proof_start
                                      8#usize)
                                  let i3 ← Slice.index_usize val4 i2
                                  let i4 ←
                                    NMT_call_3
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  if i3 != i4
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ←
                                      NMT_call_5
                                        val2
                                    let s1 ←
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    let i5 ← Slice.index_usize data 1#usize
                                    let i6 ← lift (UScalar.cast .Usize i5)
                                    let r14 ← NMT_call_11 p val1 s1 i6
                                    let cf12 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    match cf12 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val6 =>
                                      let i7 := alloc.vec.Vec.len val6
                                      let i8 := Slice.len val
                                      if i7 != i8
                                      then
                                        ok (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else ok (core.result.Result.Ok val6)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (alloc.vec.Vec Std.U8)
                                        (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          solana_program_error.ProgramError) residual
  else
    let b1 ←
      NMT_call_1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    if b1
    then
      let i := Slice.len accounts
      if i != 3#usize
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let proof_account ← Slice.index_usize accounts 0#usize
        let public_account ← Slice.index_usize accounts 1#usize
        let checkpoint_account ← Slice.index_usize accounts 2#usize
        let r ←
          NMT_call_15
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ←
            NMT_call_13 proof_account
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ←
              NMT_call_13 public_account
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ←
                NMT_call_14
                  checkpoint_account program_id true
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ←
                  (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) checkpoint_account
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← NMT_call_16 val
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ←
                      (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) public_account
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ←
                        NMT_call_12 val1
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ←
                          NMT_call_7
                            val2
                        let r9 ←
                          NMT_call_2
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ←
                            NMT_call_6
                              val2
                          let r10 ←
                            NMT_call_9
                              pvpftcv.lane_transition.candidate_afterstate
                          let r11 ←
                            NMT_call_2
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ←
                              (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10)
                                proof_account
                            let cf10 ←
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ←
                                NMT_call_4
                              let proof_start ←
                                NMT_call_8
                              let o ←
                                lift (Usize.checked_add proof_start
                                  proof_length)
                              let r13 ←
                                core.option.Option.ok_or o
                                  solana_program_error.ProgramError.InvalidAccountData
                              let cf11 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let i1 := Slice.len val4
                                if i1 != val5
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let s ←
                                    core.slice.index.Slice.index
                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                      Std.U8) val4 { «end» := proof_start }
                                  let b2 ←
                                    NMT_call_0
                                      core.cmp.PartialEqU8 s val3
                                  if b2
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ←
                                      lift (Std.Usize.wrapping_add proof_start
                                        8#usize)
                                    let i3 ← Slice.index_usize val4 i2
                                    let i4 ←
                                      NMT_call_3
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    if i3 != i4
                                    then
                                      ok (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ←
                                        NMT_call_5
                                          val2
                                      let s1 ←
                                        core.slice.index.Slice.index
                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) val4
                                          {
                                            start := proof_start,
                                            «end» := val5
                                          }
                                      let i5 ← Slice.index_usize data 1#usize
                                      let i6 ← lift (UScalar.cast .Usize i5)
                                      let r14 ← NMT_call_11 p val1 s1 i6
                                      let cf12 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf12 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val6 =>
                                        let i7 := alloc.vec.Vec.len val6
                                        let i8 := Slice.len val
                                        if i7 != i8
                                        then
                                          ok (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else ok (core.result.Result.Ok val6)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (alloc.vec.Vec Std.U8)
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
    else
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)


end PRVFresh_i1

theorem PRVEq.NMT_stage1_owned.stage1_owned_i1 :
    @NMT_stage1_owned.PRVFresh_i1.r1_pool_adapter.owned.stage1_owned =
    @NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned := rfl
#print axioms PRVEq.NMT_stage1_owned.stage1_owned_i1
end NMT_stage1_owned

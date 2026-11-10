-- PCVK_ AdapterRw stage1: fresh = gate. Fresh text: PCVJ emission (Aeneas b59d5188-extended, overflow ON, frozen 4bb3b3f), externals as fields of Ext.
-- RESULT CLASS: CONDITIONAL_ON_BINDING (see Bound). Statement: for every ops and x with Bound ops x, fresh x = gate ops.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace PCVK_S1

structure Ext where
  aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result (core.result.Result Unit aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
  aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 → Result (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES : Result Std.Usize
  solana_program_error_ProgramError_Insts_CoreCloneClone_clone : solana_program_error.ProgramError → Result solana_program_error.ProgramError
  r1_pool_adapter_owned_require_verifier_checkpoint : r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → Bool → Result (core.result.Result Unit solana_program_error.ProgramError)
  r1_pool_adapter_owned_require_distinct_accounts : ∀ {N : Std.Usize}, (Array r1_pool_adapter.owned.OwnedAccount N) → Result (core.result.Result Unit solana_program_error.ProgramError)
  r1_pool_adapter_owned_require_readonly_buffer : r1_pool_adapter.owned.OwnedAccount → Result (core.result.Result Unit solana_program_error.ProgramError)
  r1_pool_adapter_decode_public_statement_box : (Slice Std.U8) → Result (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError)
  aspis_r1_cost_probe_transport_Variant_tag : aspis_r1_cost_probe.transport.Variant → Result Std.U8
  aspis_r1_cost_probe_verifier_PROOF_BYTES : Result Std.Usize
  Slice_Insts_CoreCmpPartialEqArray_ne : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U), (Slice T) → (Array U N) → Result Bool
  Slice_Insts_CoreCmpPartialEqArray_eq : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U), (Slice T) → (Array U N) → Result Bool
  r1_pool_adapter_owned_require_zero : (Slice Std.U8) → Result (core.result.Result Unit solana_program_error.ProgramError)
  first_decoded : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice Std.U8) → (Slice Std.U8) → Std.Usize → Result (core.result.Result (alloc.vec.Vec Std.U8) solana_program_error.ProgramError)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

def r1_pool_adapter.owned.OwnedAccount.data (x : Ext)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  := do
  match self.bytes with
  | core.result.Result.Ok bytes =>
    let s := alloc.vec.Vec.deref bytes
    ok (core.result.Result.Ok s)
  | core.result.Result.Err error =>
    let pe ←
      x.solana_program_error_ProgramError_Insts_CoreCloneClone_clone error
    ok (core.result.Result.Err pe)

def
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage1_owned.closure_1)
  (tupled_args :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage1_owned.closure_1
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
}

def
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage1_owned.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage1_owned.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
}

def r1_pool_adapter.owned.stage1_owned (x : Ext)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ←
    x.Slice_Insts_CoreCmpPartialEqArray_eq core.cmp.PartialEqU8 data
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
        x.r1_pool_adapter_owned_require_distinct_accounts
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← x.r1_pool_adapter_owned_require_readonly_buffer proof_account
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ←
            x.r1_pool_adapter_owned_require_readonly_buffer public_account
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ←
              x.r1_pool_adapter_owned_require_verifier_checkpoint
                checkpoint_account program_id true
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ←
                (r1_pool_adapter.owned.OwnedAccount.data x) checkpoint_account
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← x.r1_pool_adapter_owned_require_zero val
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ←
                    (r1_pool_adapter.owned.OwnedAccount.data x) public_account
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← x.r1_pool_adapter_decode_public_statement_box val1
                    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ←
                        x.aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1
                          val2
                      let r9 ←
                        core.result.Result.map_err
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ←
                          x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common
                            val2
                        let r10 ←
                          x.aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1
                            pvpftcv.lane_transition.candidate_afterstate
                        let r11 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ←
                            (r1_pool_adapter.owned.OwnedAccount.data x)
                              proof_account
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ←
                              x.aspis_r1_cost_probe_verifier_PROOF_BYTES
                            let proof_start ←
                              x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
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
                                  x.Slice_Insts_CoreCmpPartialEqArray_ne
                                    core.cmp.PartialEqU8 s val3
                                if b1
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ← proof_start + 8#usize
                                  let i3 ← Slice.index_usize val4 i2
                                  let i4 ←
                                    x.aspis_r1_cost_probe_transport_Variant_tag
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  if i3 != i4
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ←
                                      x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public
                                        val2
                                    let s1 ←
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    let i5 ← Slice.index_usize data 1#usize
                                    let i6 ← lift (UScalar.cast .Usize i5)
                                    let r14 ← x.first_decoded p val1 s1 i6
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
      x.Slice_Insts_CoreCmpPartialEqArray_eq core.cmp.PartialEqU8 data
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
          x.r1_pool_adapter_owned_require_distinct_accounts
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ←
            x.r1_pool_adapter_owned_require_readonly_buffer proof_account
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ←
              x.r1_pool_adapter_owned_require_readonly_buffer public_account
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ←
                x.r1_pool_adapter_owned_require_verifier_checkpoint
                  checkpoint_account program_id true
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ←
                  (r1_pool_adapter.owned.OwnedAccount.data x) checkpoint_account
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← x.r1_pool_adapter_owned_require_zero val
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ←
                      (r1_pool_adapter.owned.OwnedAccount.data x) public_account
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ←
                        x.r1_pool_adapter_decode_public_statement_box val1
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ←
                          x.aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1
                            val2
                        let r9 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ←
                            x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common
                              val2
                          let r10 ←
                            x.aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1
                              pvpftcv.lane_transition.candidate_afterstate
                          let r11 ←
                            core.result.Result.map_err
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ←
                              (r1_pool_adapter.owned.OwnedAccount.data x)
                                proof_account
                            let cf10 ←
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ←
                                x.aspis_r1_cost_probe_verifier_PROOF_BYTES
                              let proof_start ←
                                x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
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
                                    x.Slice_Insts_CoreCmpPartialEqArray_ne
                                      core.cmp.PartialEqU8 s val3
                                  if b2
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ← proof_start + 8#usize
                                    let i3 ← Slice.index_usize val4 i2
                                    let i4 ←
                                      x.aspis_r1_cost_probe_transport_Variant_tag
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    if i3 != i4
                                    then
                                      ok (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ←
                                        x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public
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
                                      let r14 ← x.first_decoded p val1 s1 i6
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

structure Bound (ops : Ops) (x : Ext) : Prop where
  h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public : x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public = AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
  h_aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1 : x.aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1 = ops.op21
  h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common : x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common = AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
  h_aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 : x.aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 = ops.op24
  h_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES : x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES = AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops
  h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone : x.solana_program_error_ProgramError_Insts_CoreCloneClone_clone = ops.op35
  h_r1_pool_adapter_owned_require_verifier_checkpoint : x.r1_pool_adapter_owned_require_verifier_checkpoint = AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops
  h_r1_pool_adapter_owned_require_distinct_accounts : ∀ (N : Std.Usize), @x.r1_pool_adapter_owned_require_distinct_accounts N = @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N
  h_r1_pool_adapter_owned_require_readonly_buffer : x.r1_pool_adapter_owned_require_readonly_buffer = AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  h_r1_pool_adapter_decode_public_statement_box : x.r1_pool_adapter_decode_public_statement_box = ops.op47
  h_aspis_r1_cost_probe_transport_Variant_tag : x.aspis_r1_cost_probe_transport_Variant_tag = AdapterRw.aspis_r1_cost_probe.transport.Variant.tag
  h_aspis_r1_cost_probe_verifier_PROOF_BYTES : x.aspis_r1_cost_probe_verifier_PROOF_BYTES = AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES
  h_Slice_Insts_CoreCmpPartialEqArray_ne : ∀ (T U : Type) (N : Std.Usize) (i : core.cmp.PartialEq T U), @x.Slice_Insts_CoreCmpPartialEqArray_ne T U N i = @ops.op0 T U N i
  h_Slice_Insts_CoreCmpPartialEqArray_eq : ∀ (T U : Type) (N : Std.Usize) (i : core.cmp.PartialEq T U), @x.Slice_Insts_CoreCmpPartialEqArray_eq T U N i = @ops.op1 T U N i
  h_r1_pool_adapter_owned_require_zero : x.r1_pool_adapter_owned_require_zero = AdapterRw.r1_pool_adapter.owned.require_zero
  h_first_decoded : x.first_decoded = AdapterRw.first_decoded ops

end PCVK_S1
end AdapterRw

theorem PRVEq_usize_add_wrap (a b : Std.Usize) (h : a.val + b.val < 4294967296) :
    (a + b : Result Std.Usize) = ok (Std.Usize.wrapping_add a b) := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, Std.Usize.wrapping_add_val_eq]
  have h2 : a.val + b.val < UScalar.size UScalarTy.Usize := by
    rw [Std.Usize.max_def] at hmax
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    have := Nat.one_le_two_pow (n := Std.Usize.numBits)
    omega
  exact (Nat.mod_eq_of_lt h2).symm

theorem PRVEq_after_ex (ops : AdapterRw.Ops) :
    ∃ ps : Std.Usize, AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops = ok ps ∧ ps.val = 688 := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  have hmax : (8#usize).val + (680#usize).val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := 8#usize) (y := 680#usize) hmax)
  refine ⟨z, hz, ?_⟩
  have h8 : (8#usize).val = 8 := by scalar_tac
  have h6 : (680#usize).val = 680 := by scalar_tac
  omega

namespace PRVEq.AdapterStage1_k1
variable {ops : AdapterRw.Ops} {x : AdapterRw.PCVK_S1.Ext} (b : AdapterRw.PCVK_S1.Bound ops x)
include b

theorem data_eq :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.OwnedAccount.data x = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops := by
  funext self
  unfold AdapterRw.PCVK_S1.r1_pool_adapter.owned.OwnedAccount.data AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  rw [b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone]
  rfl

theorem stage_eq :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned x = AdapterRw.r1_pool_adapter.owned.stage1_owned ops := by
  funext program_id accounts data
  obtain ⟨ps, hps, hpsv⟩ := PRVEq_after_ex ops
  have h8 : (8#usize).val = 8 := by scalar_tac
  have hadd : (ps + 8#usize : Result Std.Usize) = ok (Std.Usize.wrapping_add ps 8#usize) :=
    PRVEq_usize_add_wrap ps 8#usize (by omega)
  unfold AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned AdapterRw.r1_pool_adapter.owned.stage1_owned
  simp only [data_eq b, b.h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public, b.h_aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common, b.h_aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1, b.h_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone, b.h_r1_pool_adapter_owned_require_verifier_checkpoint, b.h_r1_pool_adapter_owned_require_distinct_accounts, b.h_r1_pool_adapter_owned_require_readonly_buffer, b.h_r1_pool_adapter_decode_public_statement_box, b.h_aspis_r1_cost_probe_transport_Variant_tag, b.h_aspis_r1_cost_probe_verifier_PROOF_BYTES, b.h_Slice_Insts_CoreCmpPartialEqArray_ne, b.h_Slice_Insts_CoreCmpPartialEqArray_eq, b.h_r1_pool_adapter_owned_require_zero, b.h_first_decoded, hps, hadd]
  rfl

end PRVEq.AdapterStage1_k1

namespace PRVEq.AdapterStage1_k1
open AdapterRw AdapterRw.PCVK_S1
/-- Non-vacuity: for every ops there is an Ext satisfying Bound (each field is the gate counterpart). -/
theorem bound_exists (ops : Ops) : ∃ x : Ext, Bound ops x :=
  ⟨{
    aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
    aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1 := ops.op21
    aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
    aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 := ops.op24
    aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES := AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops
    solana_program_error_ProgramError_Insts_CoreCloneClone_clone := ops.op35
    r1_pool_adapter_owned_require_verifier_checkpoint := AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops
    r1_pool_adapter_owned_require_distinct_accounts := fun {N} => @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N
    r1_pool_adapter_owned_require_readonly_buffer := AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
    r1_pool_adapter_decode_public_statement_box := ops.op47
    aspis_r1_cost_probe_transport_Variant_tag := AdapterRw.aspis_r1_cost_probe.transport.Variant.tag
    aspis_r1_cost_probe_verifier_PROOF_BYTES := AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES
    Slice_Insts_CoreCmpPartialEqArray_ne := @ops.op0
    Slice_Insts_CoreCmpPartialEqArray_eq := @ops.op1
    r1_pool_adapter_owned_require_zero := AdapterRw.r1_pool_adapter.owned.require_zero
    first_decoded := AdapterRw.first_decoded ops
    }, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩⟩
end PRVEq.AdapterStage1_k1

#print axioms PRVEq_usize_add_wrap
#print axioms PRVEq_after_ex
#print axioms PRVEq.AdapterStage1_k1.data_eq
#print axioms PRVEq.AdapterStage1_k1.stage_eq
#print axioms PRVEq.AdapterStage1_k1.bound_exists

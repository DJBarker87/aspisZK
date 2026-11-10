-- PCVV_ AdapterRw callees: fresh text from PCVV_E008 (original Aeneas 959659a6, overflow ON, frozen 4bb3b3f, LLBC PCVV_E006), externals as fields of Ext.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AdapterRw
namespace PCVV_S3
def r1_pool_adapter.decode_public_statement_box.closure := Unit
def r1_pool_adapter.decode_master_box.closure := Unit
def r1_pool_adapter.decode_checkpoint_box.closure := Unit
def r1_pool_adapter.scan_proof_buffer.closure_1 := Unit
def r1_pool_adapter.scan_proof_buffer.closure := Unit
structure Ext where
  aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_statement_v1 : Slice Std.U8 → Result (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_checkpoint_v1 : Slice Std.U8 → Result (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_master_v1 : Slice Std.U8 → Result (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 → Result (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  aspis_statement_pool_v1_pair_terminal_decode_pool_v1_pair_verified_afterstate_v1 : Slice Std.U8 → Result (core.result.Result aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES : Result Std.Usize
  aspis_r1_cost_probe_verifier_Error_Insts_CoreFmtDebug_fmt : aspis_r1_cost_probe.verifier.Error → core.fmt.Formatter → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  alloc_string_String_Insts_CoreOpsDerefDerefStr_deref : String → Result Str
  aspis_r1_cost_probe_transport_Variant_tag : aspis_r1_cost_probe.transport.Variant → Result Std.U8
  aspis_r1_cost_probe_verifier_PROOF_BYTES : Result Std.Usize
  core_hint_must_use : ∀ {T : Type}, T → Result T
  solana_msg_sol_log : Str → Result Unit
  alloc_fmt_format : core.fmt.Arguments → Result String

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

@[reducible, rust_trait_impl "core::cmp::PartialEq<[@T], [@U]>"]
impl_def Slice.Insts.CoreCmpPartialEqSlice {T : Type} {U : Type}
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T)
  (Slice U) := {
  eq := core.slice.cmp.PartialEqSlice.eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice
    cmpPartialEqInst)
}

@[reducible, rust_trait_impl
  "core::fmt::Debug<aspis_r1_cost_probe::verifier::Error>"]
def aspis_r1_cost_probe.verifier.Error.Insts.CoreFmtDebug (x : Ext) : core.fmt.Debug
  aspis_r1_cost_probe.verifier.Error := {
  fmt := x.aspis_r1_cost_probe_verifier_Error_Insts_CoreFmtDebug_fmt
}

def error (x : Ext)
  (e : aspis_r1_cost_probe.verifier.Error) :
  Result solana_program_error.ProgramError
  := do
  let a ←
    core.fmt.rt.Argument.new_debug
      (aspis_r1_cost_probe.verifier.Error.Insts.CoreFmtDebug x) e
  let a1 ←
    core.fmt.Arguments.new
      (Array.make 12#usize [
        9#u8, 114#u8, 49#u8, 58#u8, 101#u8, 114#u8, 114#u8, 111#u8, 114#u8,
        58#u8, 192#u8, 0#u8
        ]) (Array.make 1#usize [ a ])
  let s ← x.alloc_fmt_format a1
  let s1 ← x.core_hint_must_use s
  let s2 ← x.alloc_string_String_Insts_CoreOpsDerefDerefStr_deref s1
  x.solana_msg_sol_log s2
  ok solana_program_error.ProgramError.InvalidInstructionData

def
  r1_pool_adapter.decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
  (c : r1_pool_adapter.decode_public_statement_box.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  : core.ops.function.FnOnce
  r1_pool_adapter.decode_public_statement_box.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
}

def r1_pool_adapter.decode_public_statement_box (x : Ext)
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    solana_program_error.ProgramError)
  := do
  let r ←
    x.aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_statement_v1
      bytes
  let r1 ←
    core.result.Result.map_err
      r1_pool_adapter.decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      (core.convert.FromSame solana_program_error.ProgramError) residual

def
  r1_pool_adapter.decode_master_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
  (c : r1_pool_adapter.decode_master_box.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.decode_master_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.decode_master_box.closure
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.decode_master_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
}

def r1_pool_adapter.decode_master_box (x : Ext)
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
    solana_program_error.ProgramError)
  := do
  let r ←
    x.aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_master_v1
      bytes
  let r1 ←
    core.result.Result.map_err
      r1_pool_adapter.decode_master_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
      (core.convert.FromSame solana_program_error.ProgramError) residual

def
  r1_pool_adapter.decode_checkpoint_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
  (c : r1_pool_adapter.decode_checkpoint_box.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.decode_checkpoint_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.decode_checkpoint_box.closure
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.decode_checkpoint_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
}

def r1_pool_adapter.decode_checkpoint_box (x : Ext)
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
    solana_program_error.ProgramError)
  := do
  let r ←
    x.aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_checkpoint_v1
      bytes
  let r1 ←
    core.result.Result.map_err
      r1_pool_adapter.decode_checkpoint_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
      (core.convert.FromSame solana_program_error.ProgramError) residual

def
  r1_pool_adapter.scan_proof_buffer.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
  (c : r1_pool_adapter.scan_proof_buffer.closure_1)
  (tupled_args :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.scan_proof_buffer.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.scan_proof_buffer.closure_1
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.scan_proof_buffer.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
}

def
  r1_pool_adapter.scan_proof_buffer.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
  (c : r1_pool_adapter.scan_proof_buffer.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.scan_proof_buffer.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.scan_proof_buffer.closure
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.scan_proof_buffer.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
}

def r1_pool_adapter.scan_proof_buffer (x : Ext)
  (bytes : Slice Std.U8) :
  Result (core.result.Result r1_pool_adapter.ScannedAsqaProof
    solana_program_error.ProgramError)
  := do
  let proof_length ← x.aspis_r1_cost_probe_verifier_PROOF_BYTES
  let i ←
    x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  let o ← lift (Usize.checked_add i proof_length)
  let r ←
    core.option.Option.ok_or o
      solana_program_error.ProgramError.InvalidAccountData
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i1 := Slice.len bytes
    if i1 != val
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let proof_start ← 0#usize + i
      let candidate_bytes ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := 0#usize, «end» := proof_start }
      let r1 ←
        x.aspis_statement_pool_v1_pair_terminal_decode_pool_v1_pair_verified_afterstate_v1
          candidate_bytes
      let r2 ←
        core.result.Result.map_err
          r1_pool_adapter.scan_proof_buffer.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
          r1 ()
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r3 ←
          x.aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1
            val1
        let r4 ←
          core.result.Result.map_err
            r1_pool_adapter.scan_proof_buffer.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
            r3 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s ← Array.Insts.CoreConvertAsRefSlice.as_ref val2
          let b ←
            core.cmp.impls.PartialEqShared.ne
              (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s
              candidate_bytes
          if b
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            let i2 ← proof_start + 8#usize
            let i3 ← Slice.index_usize bytes i2
            let i4 ←
              x.aspis_r1_cost_probe_transport_Variant_tag
                aspis_r1_cost_probe.transport.Variant.S2
            if i3 != i4
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else
              ok (core.result.Result.Ok
                { candidate_afterstate := val1, proof_length })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_pool_adapter.ScannedAsqaProof (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_pool_adapter.ScannedAsqaProof (core.convert.FromSame
          solana_program_error.ProgramError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.ScannedAsqaProof (core.convert.FromSame
      solana_program_error.ProgramError) residual

theorem decode_master_box_value (x : Ext) (b : Slice Std.U8) :
    r1_pool_adapter.decode_master_box x b =
      (do let r ← x.aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_master_v1 b
          ok (match r with
              | core.result.Result.Ok v => core.result.Result.Ok v
              | core.result.Result.Err _ => core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)) := by
  unfold r1_pool_adapter.decode_master_box
  cases h : x.aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_master_v1 b with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

theorem decode_checkpoint_box_value (x : Ext) (b : Slice Std.U8) :
    r1_pool_adapter.decode_checkpoint_box x b =
      (do let r ← x.aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_checkpoint_v1 b
          ok (match r with
              | core.result.Result.Ok v => core.result.Result.Ok v
              | core.result.Result.Err _ => core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)) := by
  unfold r1_pool_adapter.decode_checkpoint_box
  cases h : x.aspis_statement_pool_v1_pair_forest_accounts_decode_pool_v1_pair_forest_checkpoint_v1 b with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl
#print axioms decode_master_box_value
#print axioms decode_checkpoint_box_value
end PCVV_S3
end AdapterRw

import NMS_Effect242
set_option autoImplicit false
noncomputable section
namespace NMS_Effect241
open Aeneas Aeneas.Std Result AdapterRw
variable {M : Type → Type} [Monad M] [MonadLift Result M]
local instance : MonadLift Result Result where
 monadLift := id
structure Effects (M : Type → Type) where
  op11 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8) → H → (Option
        (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → M
        (core.result.Result Unit aspis_r1_cost_probe.verifier.Error)
  op22 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
        → M (core.result.Result (Array Std.U8 1880#usize)
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op44 : aspis_r1_cost_probe.verifier.Error → M
        solana_program_error.ProgramError
  op53 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
        → M (core.result.Result Unit solana_program_error.ProgramError)
  validate : solana_pubkey.Pubkey → Slice r1_pool_adapter.owned.OwnedAccount → Slice U8 →
   core.result.Result U64 solana_program_error.ProgramError → M (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError)
  data : r1_pool_adapter.owned.OwnedAccount → M (core.result.Result (Slice U8) solana_program_error.ProgramError)

/-- Full error callback, evaluated only on the actual Err arm. -/
def mapError {A : Type} (reply : core.result.Result A aspis_r1_cost_probe.verifier.Error)
 (callback : aspis_r1_cost_probe.verifier.Error → M solana_program_error.ProgramError) :
 M (core.result.Result A solana_program_error.ProgramError) :=
 match reply with
 | .Ok a => pure (.Ok a)
 | .Err e => do
   let error ← callback e
   pure (.Err error)

def stage2 (ops : Ops) (effects : Effects M)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  M (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len accounts
  if i != 7#usize
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let o ←
      core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice
        Std.U8) data { «end» := 4#usize }
    let a ←
      (pure aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC : Result (Array U8 4#usize))
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops
        Std.U8)) a ()
    let b ←
      core.cmp.PartialEq.ne.trait_default
        (core.option.Option.Insts.CoreCmpPartialEqOption ops
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice
        core.cmp.PartialEqU8))) o (some s)
    if b
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let r ←
        effects.validate program_id accounts data
          current_slot
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let oa ← Slice.index_usize accounts 0#usize
        let r1 ← effects.data oa
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let oa1 ← Slice.index_usize accounts 6#usize
          let r2 ← effects.data oa1
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let proof_start ←
              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
            let o1 ← lift (Usize.checked_add proof_start val.proof_length)
            let r3 ←
              core.option.Option.ok_or o1
                solana_program_error.ProgramError.InvalidAccountData
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let i1 := Slice.len val1
              if i1 != val3
              then
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let r4 ←
                  effects.op22
                    val.statement
                let r5 ←
                  core.result.Result.map_err
                    r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                    r4 ()
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let s1 ← lift (Array.to_slice val4)
                  let i2 := Slice.len s1
                  let i3 ←
                    (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
                  if i2 != i3
                  then
                    ok (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidInstructionData)
                  else
                    let s2 ← lift (Array.to_slice val4)
                    let s3 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                        val1 { start := proof_start, «end» := val3 }
                    let o2 ← (observer ops)
                    let r6 ←
                      effects.op11
                        (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) s2 s3 val2
                        () o2
                    let r7 ←
                      mapError r6 effects.op44
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      effects.op53 val.statement
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame solana_program_error.ProgramError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame solana_program_error.ProgramError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame solana_program_error.ProgramError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual

def raw (ops : Ops) (auth : NMS_Emitted.AuthCall) : Effects Result := {
 op11 := ops.op11
 op22 := ops.op22
 op44 := ops.op44
 op53 := ops.op53
 validate := NMS_Emitted.validate ops auth
 data := NMS_Emitted.get ops
}

theorem mapError_raw {A : Type} (reply : core.result.Result A aspis_r1_cost_probe.verifier.Error)
 (callback : aspis_r1_cost_probe.verifier.Error → Result solana_program_error.ProgramError) :
 mapError reply callback = core.result.Result.map_err
  (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error solana_program_error.ProgramError) reply callback := by
 cases reply <;> rfl
#print axioms mapError_raw

theorem erases (ops : Ops) (auth : NMS_Emitted.AuthCall)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 stage2 ops (raw ops auth) program accounts data slot =
 NMS_Emitted.stage2 ops auth program accounts data slot := by
 unfold stage2 raw NMS_Emitted.stage2
 simp only [mapError_raw]
 rfl
#print axioms erases
end NMS_Effect241

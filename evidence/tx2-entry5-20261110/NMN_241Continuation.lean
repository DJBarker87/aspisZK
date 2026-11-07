import NMN_241ValueFold
set_option autoImplicit false
noncomputable section
namespace NMN_241Continuation
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Exact continuation after the entered242 call. This is source support,
not a packet/native producer, and keeps all subsequent typed child calls. -/
def afterValidate (ops : Ops) (initial : State) (r : core.result.Result Validated PE) : Run PR := do
  let accounts := initial.frame.accounts
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s1 := {initial with validated := some val}
        let oa ← Slice.index_usize accounts 0#usize
        let r1 ← NLE_OwnedStep.proof ops s1 oa
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let s2 := {s1 with proofBytes := some val1}
          let oa1 ← Slice.index_usize accounts 6#usize
          let r2 ← NLE_OwnedStep.checkpoint ops s2 oa1
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s3 := {s2 with checkpoint := some val2}
            let proof_start ←
              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
            let o1 ← lift (Usize.checked_add proof_start val.proof_length)
            let r3 ←
              core.option.Option.ok_or o1
                solana_program_error.ProgramError.InvalidAccountData
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let s4 := {s3 with proofEnd := some val3}
              let i1 := Slice.len val1
              if i1 != val3
              then
                pure (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let r4 ←
                  NLE_OwnedStep.encode ops s4 val.statement
                let r5 ←
                  core.result.Result.map_err
                    r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                    r4 ()
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let s5 := {s4 with publicBytes := some val4}
                  let s1 ← lift (Array.to_slice val4)
                  let i2 := Slice.len s1
                  let i3 ←
                    (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
                  if i2 != i3
                  then
                    pure (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidInstructionData)
                  else
                    let s2 ← lift (Array.to_slice val4)
                    let s3 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                        val1 { start := proof_start, «end» := val3 }
                    let o2 ← (observer ops)
                    let r6 ←
                      NLE_OwnedStep.tx2 ops s5 s2 s3 val2 o2
                    let r7 ←
                      errorMap ops s5 r6
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      NLE_OwnedStep.emit ops s5 val.statement
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame solana_program_error.ProgramError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame solana_program_error.ProgramError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame solana_program_error.ProgramError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual
/-- The242 event is the SAME original-state occurrence. -/
def entered (ops : Ops) (initial : State) (reply : Result (core.result.Result Validated PE)) : Run PR :=
 NJU_Log.record (.validate initial) reply >>= afterValidate ops initial
/-- All ProgramError payloads are quantified, including arbitrary Strings.
No source getter/encoder/auth/emit suffix occurs after an Err. -/
theorem rejected (ops : Ops) (initial : State) (e : PE) :
 entered ops initial (.ok (.Err e)) = ⟨.ok (.Err e),[Event.validate initial (.ok (.Err e))]⟩ := rfl
/-- Source outer failure carries only its reached prefix. -/
theorem failed (ops : Ops) (initial : State) (e : Aeneas.Std.Error) :
 entered ops initial (.fail e) = ⟨.fail e,[Event.validate initial (.fail e)]⟩ := rfl
/-- Divergence creates no returned value or later source event. -/
theorem diverged (ops : Ops) (initial : State) :
 entered ops initial .div = ⟨.div,[Event.validate initial .div]⟩ := rfl
#print afterValidate
#print entered
#print rejected
#print failed
#print diverged
#print axioms rejected
#print axioms failed
#print axioms diverged
end NMN_241Continuation

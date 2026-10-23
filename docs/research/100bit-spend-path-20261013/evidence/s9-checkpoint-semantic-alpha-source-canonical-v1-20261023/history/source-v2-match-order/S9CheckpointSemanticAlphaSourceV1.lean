import S9CheckpointSemanticReadOnlyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckpointSemanticAlphaSourceV1
open AspisR1Stage2
open AspisR1S9CheckpointSemanticReadOnlyV1

/-- Exact generated helper body, replacing only the Reader.k callee with an
explicit operation argument. The source and transformation pins are separate. -/
def source (read : ReadK)
  (bytes : Slice Std.U8) (at1 : Std.Usize) :
  Result (core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    Std.Usize) verifier.Error)
  := do
  let (r, r1) ← read { bytes, «at» := at1 }
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r2, r3) ← read r1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r4, r5) ← read r3
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r6, r7) ← read r5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let (r8, r9) ← read r7
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (r10, r11) ← read r9
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r10
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let (r12, r13) ← read r11
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r12
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let (r14, r15) ← read r13
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r14
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  let (r16, r17) ← read r15
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r16
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val8 =>
                    let (r18, r19) ← read r17
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r18
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val9 =>
                      ok (core.result.Result.Ok
                        (Array.make 10#usize [
                           val, val1, val2, val3, val4, val5, val6, val7, val8,
                           val9
                           ], r19.«at»))
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                        (core.convert.FromSame verifier.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                      (core.convert.FromSame verifier.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                    (core.convert.FromSame verifier.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                  (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
              (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
            (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
          (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
        (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
      (core.convert.FromSame verifier.Error) residual


/-- The generated Rust Result try/FromResidual control flow is exactly its
ordinary short-circuit match. The reader continuation and all outer failures
remain untouched. This symbolic lemma avoids destructuring the ten-read spine. -/
theorem try_controlflow_eq_match {T : Type}
    (value : core.result.Result K verifier.Error)
    (next : K → Result (core.result.Result T verifier.Error)) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch value
      match cf with
      | .Continue x => next x
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          T (core.convert.FromSame verifier.Error) residual) =
    (match value with
      | .Ok x => next x
      | .Err e => .ok (.Err e)) := by
  cases value <;> rfl

/-- Full Result equality, preserving every read failure and short circuit. -/
theorem source_eq_semanticUsing (read : ReadK) (bytes : Slice U8) (start : Usize) :
    source read bytes start = semanticUsing read bytes start := by
  simp only [source,semanticUsing,withK,try_controlflow_eq_match]

#print axioms try_controlflow_eq_match
#print axioms source_eq_semanticUsing
end AspisR1S9CheckpointSemanticAlphaSourceV1

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


/-- Full Result equality, preserving every read failure and short circuit. -/
theorem source_eq_semanticUsing (read : ReadK) (bytes : Slice U8) (start : Usize) :
    source read bytes start = semanticUsing read bytes start := by
  unfold source semanticUsing
  simp only [withK]
  congr 1
  funext pair0
  rcases pair0 with ⟨result0,reader0⟩
  cases result0 with
  | Err e => rfl
  | Ok x0 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    congr 1
    funext pair1
    rcases pair1 with ⟨result1,reader1⟩
    cases result1 with
    | Err e => rfl
    | Ok x1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      congr 1
      funext pair2
      rcases pair2 with ⟨result2,reader2⟩
      cases result2 with
      | Err e => rfl
      | Ok x2 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        congr 1
        funext pair3
        rcases pair3 with ⟨result3,reader3⟩
        cases result3 with
        | Err e => rfl
        | Ok x3 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          congr 1
          funext pair4
          rcases pair4 with ⟨result4,reader4⟩
          cases result4 with
          | Err e => rfl
          | Ok x4 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            congr 1
            funext pair5
            rcases pair5 with ⟨result5,reader5⟩
            cases result5 with
            | Err e => rfl
            | Ok x5 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
              congr 1
              funext pair6
              rcases pair6 with ⟨result6,reader6⟩
              cases result6 with
              | Err e => rfl
              | Ok x6 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                congr 1
                funext pair7
                rcases pair7 with ⟨result7,reader7⟩
                cases result7 with
                | Err e => rfl
                | Ok x7 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                  congr 1
                  funext pair8
                  rcases pair8 with ⟨result8,reader8⟩
                  cases result8 with
                  | Err e => rfl
                  | Ok x8 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                    congr 1
                    funext pair9
                    rcases pair9 with ⟨result9,reader9⟩
                    cases result9 with
                    | Err e => rfl
                    | Ok x9 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                      rfl

#print axioms source_eq_semanticUsing
end AspisR1S9CheckpointSemanticAlphaSourceV1

import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderSemantic
open Aeneas Aeneas.Std Result AspisR1Stage2
def semantic (read : CheckpointBytes4Sections.ReadK)
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


/-- Kernel-checked normalization of CURRENT emitted helper, for every read
implementation, including all field-decoder errors and cursor returns. -/
theorem normalization (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8) (start : Usize) :
    semantic read bytes start=CheckpointBytes4Ops.semanticUsing read bytes start := by
  unfold semantic CheckpointBytes4Ops.semanticUsing CheckpointBytes4Ops.withK
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair0 success0
  rcases pair0 with ⟨value0,reader0⟩
  cases value0 with
  | Err e => rfl
  | Ok x0 =>
    try dsimp only
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair1 success1
    rcases pair1 with ⟨value1,reader1⟩
    cases value1 with
    | Err e => rfl
    | Ok x1 =>
      try dsimp only
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro pair2 success2
      rcases pair2 with ⟨value2,reader2⟩
      cases value2 with
      | Err e => rfl
      | Ok x2 =>
        try dsimp only
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro pair3 success3
        rcases pair3 with ⟨value3,reader3⟩
        cases value3 with
        | Err e => rfl
        | Ok x3 =>
          try dsimp only
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
          apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
          intro pair4 success4
          rcases pair4 with ⟨value4,reader4⟩
          cases value4 with
          | Err e => rfl
          | Ok x4 =>
            try dsimp only
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
            apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
            intro pair5 success5
            rcases pair5 with ⟨value5,reader5⟩
            cases value5 with
            | Err e => rfl
            | Ok x5 =>
              try dsimp only
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
              apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
              intro pair6 success6
              rcases pair6 with ⟨value6,reader6⟩
              cases value6 with
              | Err e => rfl
              | Ok x6 =>
                try dsimp only
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                intro pair7 success7
                rcases pair7 with ⟨value7,reader7⟩
                cases value7 with
                | Err e => rfl
                | Ok x7 =>
                  try dsimp only
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                  intro pair8 success8
                  rcases pair8 with ⟨value8,reader8⟩
                  cases value8 with
                  | Err e => rfl
                  | Ok x8 =>
                    try dsimp only
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                    intro pair9 success9
                    rcases pair9 with ⟨value9,reader9⟩
                    cases value9 with
                    | Err e => rfl
                    | Ok x9 =>
                      try dsimp only
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms normalization
end AspisR1.Port5Q2_ReaderSemantic
end

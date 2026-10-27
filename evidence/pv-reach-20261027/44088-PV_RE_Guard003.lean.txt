import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard003
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue (inactive : Std.Usize) (active : Array Bool 1024#usize) (rows : Std.Usize) (expander : aspis_prover.state_only_hiding.SeedExpander) (values : alloc.vec.Vec aspis_core.field.QM31) (row : Std.Usize) : Result (ControlFlow (aspis_prover.state_only_hiding.SeedExpander ×
    (alloc.vec.Vec aspis_core.field.QM31) × Std.Usize) ((core.result.Result
    (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_hiding.SeedExpander)) := do
    let b ← Array.index_usize active row
    if b
    then
      let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
      ok (cont (expander, values, row1))
    else
      if row != inactive
      then
        let (r, expander1) ←
          aspis_prover.state_only_hiding.SeedExpander.qm31 expander
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let (_, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
              aspis_core.field.QM31) values row
          let values1 := index_mut_back val
          let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
          ok (cont (expander1, values1, row1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
          ok (done (r1, expander1))
      else
        let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
        ok (cont (expander, values, row1))

def onFalse (inactive : Std.Usize) (active : Array Bool 1024#usize) (rows : Std.Usize) (expander : aspis_prover.state_only_hiding.SeedExpander) (values : alloc.vec.Vec aspis_core.field.QM31) (row : Std.Usize) : Result (ControlFlow (aspis_prover.state_only_hiding.SeedExpander ×
    (alloc.vec.Vec aspis_core.field.QM31) × Std.Usize) ((core.result.Result
    (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_hiding.SeedExpander)) := do
    let (s, deref_mut_back) ← Aeneas.Std.lift (alloc.vec.Vec.deref_mut values)
    let (r, s1) ←
      aspis_prover.state_only_hiding.balance_qm31_copy_inactive s inactive
        active
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let values1 := deref_mut_back s1
      ok (done (core.result.Result.Ok values1, expander))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      ok (done (r1, expander))

/-- Exact first guard of `aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (inactive : Std.Usize) (active : Array Bool 1024#usize) (rows : Std.Usize) (expander : aspis_prover.state_only_hiding.SeedExpander) (values : alloc.vec.Vec aspis_core.field.QM31) (row : Std.Usize) :
  aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body (inactive := inactive) (active := active) (rows := rows) (expander := expander) (values := values) (row := row) =
    (if row < rows then onTrue (inactive := inactive) (active := active) (rows := rows) (expander := expander) (values := values) (row := row) else onFalse (inactive := inactive) (active := active) (rows := rows) (expander := expander) (values := values) (row := row)) := by
  rw [aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard003

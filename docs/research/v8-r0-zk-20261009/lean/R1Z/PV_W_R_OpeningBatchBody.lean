import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
open Aeneas.Std.ControlFlow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_OpeningBatchBody
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (q : alloc.vec.Vec aspis_core.field.wide_exact.WideExact) (row : Std.Usize) :
  P (ControlFlow ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact) ×
    Std.Usize) (alloc.vec.Vec aspis_core.field.wide_exact.WideExact)) := do
  if row < 1024#usize then
    let value ← invoke "prover.opening_row" (fun ops =>
        letI : ExternalFuns := ops
        prover.opening_row coefficients gp row)
    let q1 ← invoke "alloc.vec.Vec.push" (fun ops =>
        letI : ExternalFuns := ops
        alloc.vec.Vec.push q value)
    let row1 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize))
    pure (cont (q1, row1))
  else
    pure (done q)

theorem erase_program (ops : ExternalFuns)
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (q : alloc.vec.Vec aspis_core.field.wide_exact.WideExact) (row : Std.Usize) :
  erase ops (program coefficients gp q row) =
    @prover.opening_batch_loop.body _ ops coefficients gp q row := by
  unfold program prover.opening_batch_loop.body
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro value
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro q1
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro row1
          rfl
  ·
    rfl

#print axioms erase_program
end R1Z.PV_W_R_OpeningBatchBody

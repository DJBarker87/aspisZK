import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
open Aeneas.Std.ControlFlow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_OpeningInactiveBody
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights)
  (inactive : aspis_core.field.wide_exact.WideExact) (row : Std.Usize) :
  P (ControlFlow (aspis_core.field.wide_exact.WideExact × Std.Usize)
    aspis_core.field.wide_exact.WideExact) := do
  if row < 1024#usize then
    let we ← invoke "Slice.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Slice.index_usize q row)
    let q1 ← invoke "weights.Weights.raw" (fun ops =>
        letI : ExternalFuns := ops
        weights.Weights.raw w 0#usize row)
    let we1 ← invoke "aspis_core.field.wide_exact.WideExact.mul_qm31" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul_qm31 we q1)
    let inactive1 ← invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.add inactive we1)
    let row1 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize))
    pure (cont (inactive1, row1))
  else
    pure (done inactive)

theorem erase_program (ops : ExternalFuns)
  (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights)
  (inactive : aspis_core.field.wide_exact.WideExact) (row : Std.Usize) :
  erase ops (program q w inactive row) =
    @prover.opening_inactive_loop.body _ ops q w inactive row := by
  unfold program prover.opening_inactive_loop.body
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro we
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
        · intro we1
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro inactive1
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
end R1Z.PV_W_R_OpeningInactiveBody

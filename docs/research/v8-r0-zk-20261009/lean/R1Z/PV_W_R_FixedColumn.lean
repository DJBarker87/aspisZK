import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_FixedColumn
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (values : Slice aspis_core.field.QM31) :
  P (Array aspis_core.field.QM31 1024#usize) := do
  let q ← invoke "aspis_core.field.QM31.ZERO" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.QM31.ZERO)
  let out := Array.repeat 1024#usize q
  invoke "prover.fixed_k_column_loop" (fun ops =>
    letI : ExternalFuns := ops
    prover.fixed_k_column_loop values out 0#usize)

theorem erase_program (ops : ExternalFuns)
  (values : Slice aspis_core.field.QM31) :
  erase ops (program values) =
    @prover.fixed_k_column _ ops values := by
  unfold program prover.fixed_k_column
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro q
    try dsimp only
    exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_FixedColumn

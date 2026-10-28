import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_034
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (values : Slice aspis_core.field.M31) (masks : Array Std.U16 64#usize) :
  Logged aspis_core.field.M31
  := do
  let _ ← observe .balanceAudit 0 (ok ())
  let sum ← aspis_core.field.M31.ZERO
  prover.inactive_sum_m31_loop values masks sum 0#usize

theorem complete_result
  (values : Slice aspis_core.field.M31) (masks : Array Std.U16 64#usize) :
  erase (produce values masks) = prover.inactive_sum_m31 values masks := by
  unfold produce prover.inactive_sum_m31
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_034

import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_055
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (mask_sum : aspis_core.field.QM31)
  (dc : Array aspis_core.field.QM31 1024#usize) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← host_semantic.d_tail_side dc 0#usize
  let first ← aspis_core.field.QM31.mul_m31 q 512#u32
  let mask_sum1 ← aspis_core.field.QM31.add mask_sum first
  let q1 ← host_semantic.d_tail_side dc 28#usize
  let second ← aspis_core.field.QM31.mul_m31 q1 512#u32
  aspis_core.field.QM31.add mask_sum1 second

theorem complete_result
  (mask_sum : aspis_core.field.QM31)
  (dc : Array aspis_core.field.QM31 1024#usize) :
  erase (produce mask_sum dc) = host_semantic.add_d_tail mask_sum dc := by
  unfold produce host_semantic.add_d_tail
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_055

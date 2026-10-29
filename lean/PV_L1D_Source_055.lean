import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_055
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (mask_sum : aspis_core.field.QM31)
  (dc : Array aspis_core.field.QM31 1024#usize) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← PV_L1D_Logged.lift (host_semantic.d_tail_side dc 0#usize)
  let first ← PV_L1D_Logged.lift (aspis_core.field.QM31.mul_m31 q 512#u32)
  let mask_sum1 ← PV_L1D_Logged.lift (aspis_core.field.QM31.add mask_sum first)
  let q1 ← PV_L1D_Logged.lift (host_semantic.d_tail_side dc 28#usize)
  let second ← PV_L1D_Logged.lift (aspis_core.field.QM31.mul_m31 q1 512#u32)
  aspis_core.field.QM31.add mask_sum1 second

theorem complete_result
  (mask_sum : aspis_core.field.QM31)
  (dc : Array aspis_core.field.QM31 1024#usize) :
  erase (produce mask_sum dc) = host_semantic.add_d_tail mask_sum dc := by
  unfold produce
  conv_rhs => unfold host_semantic.add_d_tail
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_055

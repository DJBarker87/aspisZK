import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_048
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (coefficients : Array aspis_core.field.QM31 1024#usize)
  (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let sum ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
  host_semantic.extra_loop0 sum coefficients a b sum 0#usize

theorem complete_result
  (coefficients : Array aspis_core.field.QM31 1024#usize)
  (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
  erase (produce coefficients a b) = host_semantic.extra coefficients a b := by
  unfold produce
  conv_rhs => unfold host_semantic.extra
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
end PV_L1D_Source_048

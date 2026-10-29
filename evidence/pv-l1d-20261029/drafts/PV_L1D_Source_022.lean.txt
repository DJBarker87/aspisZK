import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_022
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (row : Std.Usize) :
  Logged aspis_core.field.wide_exact.WideExact
  := do
  let _ ← observe .opening 0 (ok ())
  let value ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.ZERO)
  prover.opening_row_loop coefficients gp row value 0#usize

theorem complete_result
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (row : Std.Usize) :
  erase (produce coefficients gp row) = prover.opening_row coefficients gp row := by
  unfold produce
  conv_rhs => unfold prover.opening_row
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
end PV_L1D_Source_022

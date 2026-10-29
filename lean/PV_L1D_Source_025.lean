import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_025
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) :
  Logged (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact
    1024#usize))
  := do
  let _ ← observe .opening 0 (ok ())
  let i := Slice.len messages
  let coefficients :=
    alloc.vec.Vec.with_capacity (Array aspis_core.field.wide_exact.WideExact
      1024#usize) i
  prover.opening_coefficients_loop variant messages coefficients 0#usize

theorem complete_result
  (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) :
  erase (produce variant messages) = prover.opening_coefficients variant messages := by
  unfold produce
  conv_rhs => unfold prover.opening_coefficients
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
end PV_L1D_Source_025

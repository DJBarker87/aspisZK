import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_Source_053
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_054
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (dc : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← PV_L1_Logged.lift (Array.index_usize dc offset)
  PV_L1_Source_053.produce dc offset 0#usize q

theorem complete_result
  (dc : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize) :
  erase (produce dc offset) = host_semantic.d_tail_side dc offset := by
  unfold produce
  conv_rhs => unfold host_semantic.d_tail_side
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_053.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_053.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_053.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_054

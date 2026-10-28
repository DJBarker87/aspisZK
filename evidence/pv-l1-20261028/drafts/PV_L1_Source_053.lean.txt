import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_053
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (dc : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize)
  (j : Std.Usize) (sum : aspis_core.field.QM31) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  if j = 28#usize
  then Pure.pure sum
  else
    let i ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add offset j))
    let q ← PV_L1_Logged.lift (Array.index_usize dc i)
    let next ← PV_L1_Logged.lift (aspis_core.field.QM31.add sum q)
    let i1 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add j 1#usize))
    host_semantic.d_tail_sum dc offset i1 next

theorem complete_result
  (dc : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize)
  (j : Std.Usize) (sum : aspis_core.field.QM31) :
  erase (produce dc offset j sum) = host_semantic.d_tail_sum dc offset j sum := by
  unfold produce
  conv_rhs => unfold host_semantic.d_tail_sum
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_053

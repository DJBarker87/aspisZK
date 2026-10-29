import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_039
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (noised : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) :
  Logged (Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let c1 ← PV_L1D_Logged.lift (core.default.DefaultArray.default 26#usize
      (alloc.vec.Vec.Insts.CoreDefaultDefault aspis_core.field.M31))
  let (c11, i) ← PV_L1D_Logged.lift (host_semantic.clone_semantic_columns_loop0 noised c1 0#usize)
  host_semantic.clone_semantic_columns_loop1 mask_only c11 i

theorem complete_result
  (noised : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) :
  erase (produce noised mask_only) = host_semantic.clone_semantic_columns noised mask_only := by
  unfold produce
  conv_rhs => unfold host_semantic.clone_semantic_columns
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
end PV_L1D_Source_039

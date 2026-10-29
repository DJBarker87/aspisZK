import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_045
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (variant : transport.Variant) (z : aspis_core.circle.SecureCirclePoint) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let bytes := alloc.vec.Vec.with_capacity Std.U8 928#usize
  host_semantic.endpoint_bytes_loop columns variant z bytes 0#usize

theorem complete_result
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (variant : transport.Variant) (z : aspis_core.circle.SecureCirclePoint) :
  erase (produce columns variant z) = host_semantic.endpoint_bytes columns variant z := by
  unfold produce
  conv_rhs => unfold host_semantic.endpoint_bytes
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
end PV_L1D_Source_045

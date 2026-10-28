import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_065
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  Logged (core.result.Result (Array aspis_core.field.QM31 29#usize)
    r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← PV_L1_Logged.lift (aspis_core.field.QM31.ZERO)
  let claims := Array.repeat 29#usize q
  let (claims1, pending_return) ← PV_L1_Logged.lift (host_semantic.claims_at_point_loop columns point claims 0#usize)
  match pending_return with
  | none => Pure.pure (core.result.Result.Ok claims1)
  | some r => Pure.pure r

theorem complete_result
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  erase (produce columns point) = host_semantic.claims_at_point columns point := by
  unfold produce
  conv_rhs => unfold host_semantic.claims_at_point
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
end PV_L1_Source_065

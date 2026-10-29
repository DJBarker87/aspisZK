import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_065
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
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
  let q ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
  let claims := Array.repeat 29#usize q
  let (claims1, pending_return) ← PV_L1D_Logged.lift (host_semantic.claims_at_point_loop columns point claims 0#usize)
  match pending_return with
  | none => Pure.pure (core.result.Result.Ok claims1)
  | some r => Pure.pure r

theorem complete_result
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  erase (produce columns point) = host_semantic.claims_at_point columns point := by
  unfold produce
  conv_rhs => unfold host_semantic.claims_at_point
  simp only [erase_bind,erase_observe,erase_lift,Aeneas.Std.bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero hz
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨claims,pending⟩ hr
  cases pending <;> rfl
#print axioms complete_result
end PV_L1D_Source_065

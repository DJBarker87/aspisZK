import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_049
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (variant : transport.Variant) (a : aspis_core.field.QM31)
  (b : aspis_core.field.QM31) :
  Logged (Array aspis_core.field.QM31 29#usize)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← PV_L1_Logged.lift (aspis_core.field.QM31.ZERO)
  let extras := Array.repeat 29#usize q
  host_semantic.extra_claims_loop columns variant a b extras 0#usize

theorem complete_result
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (variant : transport.Variant) (a : aspis_core.field.QM31)
  (b : aspis_core.field.QM31) :
  erase (produce columns variant a b) = host_semantic.extra_claims columns variant a b := by
  unfold produce
  conv_rhs => unfold host_semantic.extra_claims
  simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_049

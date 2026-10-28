import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_011
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (accepted : Array Std.U32 22#usize) (n : Std.Usize) (candidate : Std.U32) :
  Logged Bool
  := do
  let _ ← observe .queryScan 0 (ok ())
  let pending_return ←
    host_transcript.query_contains_loop accepted n candidate 0#usize
  match pending_return with
  | none => ok false
  | some b => ok b

theorem complete_result
  (accepted : Array Std.U32 22#usize) (n : Std.Usize) (candidate : Std.U32) : :
  erase (produce accepted n candidate) = host_transcript.query_contains accepted n candidate := by
  unfold produce host_transcript.query_contains
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_011

import NLE_AuthParse
set_option autoImplicit false
noncomputable section
namespace NLE_Auth
open Aeneas Aeneas.Std Result VTop_Stages
/-- Occurrence 1 retains the SAME observer and Parsed phase and full reply. -/
theorem mark_result {H : Type} (ops : Ops) (s : State H) :
 (mark ops s).result = (ops.op13 s.frame.observer .Parsed >>= fun _ => ok s) := by
 unfold mark
 rw [NJU_Log.erase_bind]
 rfl
theorem mark_events {H : Type} (ops : Ops) (s : State H) :
 (mark ops s).events = [.mark s.frame.observer (ops.op13 s.frame.observer .Parsed)] := by
 unfold mark
 cases h : ops.op13 s.frame.observer .Parsed <;> rfl
/-- Occurrence 2 forwards the whole immutable frame without a fresh witness. -/
theorem common_result {H : Type} (child : Common H) (s : State H) :
 (common child s).result = child s.frame := rfl
/-- An outer abort in the marker has no common-call suffix. -/
theorem mark_abort {H : Type} (ops : Ops) (child : Common H) (s : State H)
 (err : Error) (failed : ops.op13 s.frame.observer .Parsed = .fail err) :
 (do let next ← mark ops s; common child next) =
 (⟨.fail err,[.mark s.frame.observer (.fail err)]⟩ : Run H Reply) := by
 unfold mark
 rw [failed]
 rfl
#print mark_result
#print common_result
#print mark_abort
#print axioms mark_result
#print axioms mark_events
#print axioms common_result
#print axioms mark_abort
end NLE_Auth

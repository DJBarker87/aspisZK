import NLE_AuthMark
set_option autoImplicit false
noncomputable section
namespace NLE_Auth
open Aeneas Aeneas.Std Result VTop_Stages
/-- Local chronological fold, same shape as NHZ_DRIVER.events_from_cuts,
using typed call events rather than flattening the child's opaque effects. -/
theorem fold_source {H : Type} (ops : Ops) (child : Common H) (s : State H) :
 (G ops child s).result = source ops child s := by
 unfold G source parse mark common
 cases h : ops.op3 s.frame.proof with
 | fail err => rfl
 | div => rfl
 | ok reply =>
  cases reply with
  | Err err => rfl
  | Ok variant =>
   cases ops.op13 s.frame.observer .Parsed <;> rfl
/-- Intermediate source packet only. This parameter is exactly the missing
complete common continuation at SAME inputs; it is forbidden in a row root. -/
def CommonResultPacket {H : Type} (ops : Ops) (child : Common H) : Prop :=
 ∀ f, child f = verifier.candidate.tx2_common ops f.digest
  f.publicBytes f.proof f.checkpoint f.hash f.observer

theorem parameterized_fold {H : Type} (ops : Ops) (child : Common H)
 (packet : CommonResultPacket ops child) (s : State H) :
 (G ops child s).result = verifier.candidate.tx2_authenticated ops s.frame.digest
  s.frame.publicBytes s.frame.proof s.frame.checkpoint s.frame.hash s.frame.observer := by
 rw [fold_source]
 unfold source verifier.candidate.tx2_authenticated
 rw [packet]
 cases h : ops.op3 s.frame.proof with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
#print fold_source
#print CommonResultPacket
#print parameterized_fold
#print axioms fold_source
#print axioms parameterized_fold
end NLE_Auth

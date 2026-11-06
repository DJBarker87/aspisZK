import NLE_OwnedState
set_option autoImplicit false
noncomputable section
namespace NLE_ErrorPrefix
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Every Rust error variant reaches exactly the conversion event, even when
conversion aborts; no emit suffix or fabricated successful conversion. -/
theorem abort (ops : Ops) (state : State) (err : aspis_r1_cost_probe.verifier.Error)
 (failure : Error) (failed : ops.op44 err = .fail failure) :
 errorMap ops state (.Err err) =
 ⟨.fail failure,[Event.error state err (.fail failure)]⟩ := by
 simp only [errorMap]
 rw [failed]
 rfl
theorem diverge (ops : Ops) (state : State) (err : aspis_r1_cost_probe.verifier.Error)
 (failed : ops.op44 err = .div) :
 errorMap ops state (.Err err) = ⟨.div,[Event.error state err .div]⟩ := by
 simp only [errorMap]
 rw [failed]
 rfl
theorem rejected (ops : Ops) (state : State) (err : aspis_r1_cost_probe.verifier.Error)
 (converted : PE) (returned : ops.op44 err = ok converted) :
 errorMap ops state (.Err err) =
 ⟨ok (.Err converted),[Event.error state err (ok converted)]⟩ := by
 simp only [errorMap]
 rw [returned]
 rfl
#print abort
#print diverge
#print rejected
#print axioms abort
#print axioms diverge
#print axioms rejected
end NLE_ErrorPrefix
